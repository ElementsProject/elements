New RPCs
--------

- The new `getnodegeneration` RPC returns a process-scoped `startup_id`, a
  monotonic `chainstate_revision`, and the active tip height and hash. Callers
  can use these fields to detect daemon restarts, stale responses, and active
  chain ABA changes.
