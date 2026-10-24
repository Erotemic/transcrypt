# 03. Git operations, state machine, and failure semantics

**Status:** normative TARGET abstract behavior; individual I/O primitives
remain trusted adapters until separately verified. Cryptographic byte
calculations are defined in [02](02-protocol-and-wire-format.md).

## 1. Abstract state

Model a repository as:

```text
RepoState = {
  committed_tree: GitTree,
  index: GitIndex,
  worktree: FileSystemTree,
  attributes: AttributesSnapshot,
  public_metadata: MetadataInEachTree,
  local_git_config: GitConfig,
  credential_state: LocalCredentials,
  installed_filters: FilterConfig,
  installed_hooks: HookConfig,
  textconv_cache_refs: GitRefs,
  transaction_journal: OptionalJournal,
  context_registry: ContextAssignments
}
```

`committed_tree`, `index`, and `worktree` are **different snapshots**.
`public_metadata` may differ in each snapshot; a pre-commit check must examine
`index`, whereas `clean` normally uses the active repository's committed /
working metadata as documented by its caller. Operations must never silently
combine a working-tree salt with staged ciphertext encrypted under a different
salt. A `ContextAssignments` view is derived from Git attributes and is
explicitly pinned to the tree being validated, not ambient global config.

The **key invariant** `StageOK(index)` means:

1. For each staged protected path, its staged context is valid and has
   exactly one staged public crypto configuration for its secure format.
2. Every staged protected blob is either a canonically authenticated
   ciphertext under those parameters or an explicitly allowed legacy object
   under a separately checked policy.
3. Staged crypto-config changes cannot make previously staged encrypted
   objects undecipherable. Any transition of key-bearing metadata is
   represented by a full-tree migration/rekey rather than a lone config edit.
4. Every index path is processed as opaque bytes; a newline, space, or
   encoding edge case must not change the set of verified paths.
5. Missing local credentials or unavailable cryptography causes rejection
   of an operation requiring validation. It is not permission to skip it.

**Boundary:** a pre-commit hook is only a local guard. A malicious writer can
skip hooks. A policy that *every remote commit* is `StageOK` requires a remote
validator / protected merge workflow as an additional trusted system.

## 2. Pure effect-independent operations

Formalize pure functions before any real Git commands:

```text
classify_repo(staged_tree, committed_tree, attributes) ->
  Unencrypted | Legacy | Secure(format_id) | Mixed | Invalid(reason)

plan_init(snapshot, input_settings) -> TransactionPlan | Error
plan_unlock(snapshot, credential_candidate) -> TransactionPlan | Error
plan_rekey(snapshot, new_secret, opts) -> TransactionPlan | Error
plan_migration(snapshot, format_target, opts) -> TransactionPlan | Error
check_stage(staged_tree, attributes, metadata, secret_handle) -> OK | Error
```

These are **plans**; plans cannot write files, run programs, log secrets or
emit plaintext. The Rust pure policy kernel can be extracted with Aeneas.
The Bash implementation maps the same decision table with a hand-reviewed
case analysis.

## 3. `clean` (working bytes -> index bytes)

Precondition: the path resolves to the expected encrypted context; required
metadata and credentials are available; crypto capability is supported.

1. Parse and validate the selected config, including work factor bounds.
2. Distinguish plaintext from *valid* already-encrypted input under an
   explicit spec policy. A superficial magic-prefix check is insufficient.
   If a plaintext file begins with the magic bytes, resolve the collision
   according to a frozen, tested rule; never risk committing it as ciphertext.
3. Seal plaintext using the normative deterministic authenticated format, or
   return the identical canonical ciphertext only after full verification.
4. On success emit only complete valid ciphertext. On failure, exit nonzero
   with **zero bytes emitted**, and ensure `filter.*.required=true` so Git
   treats failures as errors.

Do not allow fallback to legacy when secure config exists but fails.
`clean` itself does not guarantee the global `StageOK` invariant if a user
manually bypasses the filter; stage validation is a separate guard.

## 4. `smudge` (Git blob -> working bytes)

Precondition: recognized version and trusted local credential/context
assignment. Parse/validate the entire ciphertext, authenticate its record
and associated data before any plaintext is emitted. For large files this
requires buffering or a protected temporary output that is not made visible
before success. On failure output no plaintext and do not overwrite a
previous valid destination. Return nonzero so required filters fail closed.
A clone missing its config fails **before persisting** a guessed password.

`textconv` is a different local display function: Git may call it with
working-tree plaintext or stored ciphertext. It can display plaintext to the
local authorized user, but may not persist cached textconv output in Git
notes/objects. `diff.*.cachetextconv` is disabled for secure formats.

## 5. Initialization and credential unlock

**Classify** by actual protected Git objects and metadata, not `HEAD` existence.
A normal Git repo with preexisting unencrypted README is eligible for secure
new-repo initialization. A legacy encrypted repo is not.

**Initialize new:** read all contexts and attributes; validate capabilities
and filesystem destinations; generate random public metadata; prepare Git
filter definitions and private credential state; build/validate the staged
metadata and any affected encrypted objects; commit all local effects only
when checks succeed; make the required committed metadata visible to the
user or stage it in a documented, reviewed manner. No false promise that
`git init` itself creates a repository commit.

**Unlock clone:** read committed/staged public metadata; preflight a known
ciphertext sample (or an explicitly authenticated repository verifier) with
the proposed credential; only after success persist local helper/filter
installation and credential settings. Wrong-password failure must leave the
previous local state intact so an immediate retry works. Repositories with
no authenticated nonempty sample require a separately specified proof-of-key
mechanism; do not accept an arbitrary password as verified.

If the user elects persistence, the storage location, file permissions,
process/daemon lifecycle, and key exposure boundary must be documented.
The modern profile must not place the secret in process argv or log text.

## 6. Rekey and migration

**Preflight** must reject or explicitly resolve: dirty staged/worktree state,
merge conflicts, unknown contexts, concurrent migration, invalid metadata,
unavailable decryption keys, unsupported crypto suites, missing named-context
secrets, symlink destination, linked Git worktrees or index path ambiguity.
Specify the outcome per case rather than taking a best-effort guess.

**Prepare** in a separate area/temporary Git index:

1. Pin source commit/tree and attributes snapshot; enumerate protected paths
   using NUL-safe Git interfaces and include every configured context.
2. Verify all source ciphertext **actually decrypts/authenticates** under
   old credentials. A no-op `clean` roundtrip of undecipherable ciphertext
   does not count as migration.
3. Generate new parameters (including a new public salt for rekey by
   default), and re-encrypt every protected blob in each applicable context.
4. Construct the new staged public config and new staged tree using the
   same immutable parameters. `StageOK` must pass for the whole candidate.
5. Validate expected plaintext preservation, context mapping, and new-key
   unlock in an independent fresh repository fixture where feasible.

**Commit:** update the affected index, metadata, and local configuration
through a defined transaction boundary. Atomic rename or Git ref compare-
and-swap where available; verify no concurrent source snapshot change;
retain explicit rollback/recovery data. At failure before publication,
leave the original index and credentials usable. Crash recovery is an
explicit state transition, not an unsupported claim of global filesystem
atomicity. A commit rewrites current-state ciphertext, not prior history.

**Post-migration:** disable creation of new textconv caches, enumerate all
old cached notes refs including named contexts, identify reachable vs
unreachable plaintext objects and report safe cleanup actions. Do not
unilaterally prune unrelated unreachable Git objects or claim to delete
remote backups/history.

## 7. Safe filesystem / Git APIs

- All path APIs use byte-safe NUL-delimited records (when serialized).
  Quoting shell strings is not sufficient for paths with newlines.
- Config writes must not traverse symlink ancestors; use secure no-follow
  primitives when available. Merely checking a symlink then writing is
  subject to TOCTOU. If zero-dependency Bash cannot guarantee no-follow
  under concurrent attacker-controlled filesystem changes, state that
  limit and fail closed for unsupported high-risk scenarios.
- Git worktrees may use `.git` as a file, not a directory. Use
  `git rev-parse --git-dir`/`--git-common-dir` carefully and distinguish
  common versus per-worktree state.
- GPG/key export, hooks, merges, and Git aliases are part of the observable
  CLI; design their secure-format behavior, or explicitly mark them
  unsupported until their own tests are added.
- Never write secrets to tempfile names, environment diagnostics, tracing,
  process argv, or Git logs. If secrets must exist in protected files or
  memory, identify their lifecycle and who can read them.

## 8. Minimal transition proof properties

```text
unlock_wrong_password(snapshot) = Error
   => observable_persistent_state_after = snapshot

migrate(snapshot) = Success(new_state)
   => StageOK(new_state.index)
   AND for every protected path p:
       authenticated_open(new_state[p], new_secret) =
       authenticated_open(snapshot[p], old_secret)

rekey(snapshot) = Error
   => candidate_index_not_published

smudge(ciphertext) = Error
   => bytes_released_to_stdout = []
```

These are target propositions for the abstract effect model. The proof must
state which Git/filesystem adapter operations are assumed atomic/correct;
Aeneas does not prove Git or kernel syscalls by translating a pure planner.
