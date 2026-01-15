# Tzimtzum v2.3 -- Scenario Walkthroughs

Concrete traces through the protocol's 9 actions. Each scenario shows
every action fired, the three-check gate evaluation, and the state after
each step.

## Shared Universe

### Tools

| Tool | conf_floor | endorsed | egress | requires |
|------|-----------|----------|--------|----------|
| `read-db` | sensitive | no | -- | `db_read` |
| `send-email` | public | no | `network_external` | `email_send` |
| `search-web` | public | yes | `network_external` | `web_access` |
| `summarize` | public | yes | -- | -- |
| `post-slack` | public | no | `network_external` | `messaging` |
| `read-file` | internal | no | -- | `fs_read` |
| `query-api` | sensitive | no | `network_internal` | `api_access` |

### Flow Policy

| (level, egress) | mode |
|-----------------|------|
| (public, network_external) | ALLOW |
| (internal, network_external) | INSPECT |
| (sensitive, network_external) | **DENY** |
| (public, network_internal) | ALLOW |
| (internal, network_internal) | ALLOW |
| (sensitive, network_internal) | INSPECT |

Unlisted pairs default to **DENY**.

### How to Read the Gate Checks

Every `invoke_start` evaluates three independent checks:

1. **Check 1 (Capability)**: agent holds every capability the tool requires
2. **Check 2 (Flow gate)**: three sub-checks ensuring no (taint, egress) pair violates policy
   - **2a**: existing speculative taint vs. new tool's egress
   - **2b**: new tool's potential taint vs. existing in-flight tools' egress
   - **2c**: new tool's own taint vs. its own egress (self-flow)
3. **Check 3 (Authorizer)**: external policy engine says yes

---

## Scenario 1: Simple Search

> An agent invokes an endorsed tool with no prior taint. The fast path --
> every check is trivially satisfied.

**Agents**: `root` -> `assistant` (holds `{web_access}`)

```mermaid
sequenceDiagram
    participant A as assistant
    participant P as Protocol
    participant T as search-web

    A->>P: invoke_start(assistant, search-web, inv1)
    Note over P: Check 1: web_access in {web_access} -- pass
    Note over P: Check 2a: speculative_taint = {} -- nothing to check
    Note over P: Check 2b: no in-flight tools -- nothing to check
    Note over P: Check 2c: search-web is endorsed -- skip
    Note over P: Check 3: authorizer_allows -- pass
    P-->>A: inv1 is now in-flight

    T-->>P: search results
    P->>A: invoke_complete(assistant, inv1)
    Note over P: search-web is endorsed -- no taint added
```

| Step | Action | in_flight | taint | speculative_taint |
|------|--------|-----------|-------|-------------------|
| 0 | -- | `{}` | `{}` | `{}` |
| 1 | `invoke_start(search-web, inv1)` | `{inv1}` | `{}` | `{}` |
| 2 | `invoke_complete(inv1)` | `{}` | `{}` | `{}` |

**Takeaway**: Endorsed tools are the fast path. No taint accumulates,
so future invocations face zero flow gate friction.

---

## Scenario 2: Read Then Search (INSPECT Mode)

> An agent reads a local file (gaining `internal` taint), then searches
> the web. The flow gate evaluates `(internal, network_external) = INSPECT`
> and the content gate certifies the search query doesn't leak the file data.

**Agents**: `root` -> `assistant` (holds `{fs_read, web_access}`)

```mermaid
sequenceDiagram
    participant A as assistant
    participant P as Protocol
    participant F as read-file
    participant W as search-web

    A->>P: invoke_start(assistant, read-file, inv1)
    Note over P: Check 1: fs_read -- pass
    Note over P: Check 2a: speculative_taint = {} -- skip
    Note over P: Check 2c: not endorsed, no egress -- no pairs
    Note over P: Check 3: authorizer -- pass
    P-->>A: inv1 in-flight

    F-->>P: file contents
    P->>A: invoke_complete(assistant, inv1)
    Note over P: not endorsed, conf_floor=internal -- taint += {internal}

    A->>P: invoke_start(assistant, search-web, inv2)
    Note over P: Check 1: web_access -- pass
    Note over P: Check 2a: taint={internal}, egress=network_external
    Note over P: (internal, network_external) = INSPECT
    Note over P: content_gate_passes(assistant, search-web) = true -- pass
    Note over P: Check 2c: endorsed -- skip
    Note over P: Check 3: authorizer -- pass
    P-->>A: inv2 in-flight

    W-->>P: search results
    P->>A: invoke_complete(assistant, inv2)
    Note over P: endorsed -- no taint added
```

| Step | Action | in_flight | taint | speculative_taint |
|------|--------|-----------|-------|-------------------|
| 0 | -- | `{}` | `{}` | `{}` |
| 1 | `invoke_start(read-file, inv1)` | `{inv1}` | `{}` | `{internal}` |
| 2 | `invoke_complete(inv1)` | `{}` | `{internal}` | `{internal}` |
| 3 | `invoke_start(search-web, inv2)` | `{inv2}` | `{internal}` | `{internal}` |
| 4 | `invoke_complete(inv2)` | `{}` | `{internal}` | `{internal}` |

**Takeaway**: INSPECT is the graduated middle ground between ALLOW and DENY.
The content gate (deterministic inspection pipeline) certifies the outgoing
arguments don't contain the tainted data. If the content gate fails,
the invocation is blocked -- same as DENY for that specific call.

---

## Scenario 3: Parallel Safe Invocations

> An agent starts `read-file` and `summarize` concurrently. Speculative
> taint from the in-flight `read-file` is conservative but doesn't block
> `summarize` because it has no egress channel.

**Agents**: `root` -> `assistant` (holds `{fs_read}`)

```mermaid
sequenceDiagram
    participant A as assistant
    participant P as Protocol
    participant F as read-file
    participant S as summarize

    A->>P: invoke_start(assistant, read-file, inv1)
    Note over P: All checks pass (no taint, no egress)
    P-->>A: inv1 in-flight

    A->>P: invoke_start(assistant, summarize, inv2)
    Note over P: Check 2a: speculative_taint={internal} (from inv1)
    Note over P: summarize has no egress -- no (level, egress) pairs
    Note over P: Check 2b: inv1 in-flight, read-file has no egress -- skip
    Note over P: Check 2c: summarize is endorsed -- skip
    P-->>A: inv2 in-flight

    S-->>P: summary
    P->>A: invoke_complete(assistant, inv2)
    Note over P: endorsed -- no taint

    F-->>P: file contents
    P->>A: invoke_complete(assistant, inv1)
    Note over P: not endorsed -- taint += {internal}
```

| Step | Action | in_flight | taint | speculative_taint |
|------|--------|-----------|-------|-------------------|
| 0 | -- | `{}` | `{}` | `{}` |
| 1 | `invoke_start(read-file, inv1)` | `{inv1}` | `{}` | `{internal}` |
| 2 | `invoke_start(summarize, inv2)` | `{inv1, inv2}` | `{}` | `{internal}` |
| 3 | `invoke_complete(inv2)` | `{inv1}` | `{}` | `{internal}` |
| 4 | `invoke_complete(inv1)` | `{}` | `{internal}` | `{internal}` |

**Takeaway**: Speculative taint is conservative (worst-case from all
in-flight non-endorsed tools) but precise about what it blocks. Tools
without egress never conflict with taint, so they always run in parallel
with anything.

---

## Scenario 4: Delegation with Endorsed Return

> Assistant delegates a researcher child for web search. The child uses
> only endorsed tools, so the parent receives zero taint on return.

**Agents**: `root` -> `assistant` (holds `{web_access}`) -> `researcher`

```mermaid
sequenceDiagram
    participant A as assistant
    participant P as Protocol
    participant C as researcher

    A->>P: delegate(assistant, researcher)
    Note over P: assistant active, researcher fresh -- pass
    P-->>C: researcher active, caps={}

    A->>P: grant_capability(assistant, researcher, web_access)
    Note over P: assistant holds web_access -- pass
    P-->>C: caps={web_access}

    C->>P: invoke_start(researcher, search-web, inv1)
    Note over P: All checks pass
    P-->>C: inv1 in-flight
    P->>C: invoke_complete(researcher, inv1)
    Note over P: endorsed -- no taint

    C->>P: invoke_start(researcher, summarize, inv2)
    P-->>C: inv2 in-flight
    P->>C: invoke_complete(researcher, inv2)
    Note over P: endorsed -- no taint

    C->>P: return_endorsed(researcher, assistant)
    Note over P: researcher in-flight={} -- pass
    Note over P: researcher taint={} -- endorsed return
    Note over P: assistant taint unchanged
    P-->>A: bounded result (no taint transfer)

    A->>P: revoke(assistant, researcher)
    Note over P: researcher deactivated, state cleaned
```

| Step | Action | researcher active | researcher taint | assistant taint |
|------|--------|:-:|:-:|:-:|
| 0 | -- | no | -- | `{}` |
| 1 | `delegate` | yes | `{}` | `{}` |
| 2 | `grant_capability(web_access)` | yes | `{}` | `{}` |
| 3 | `invoke_start(search-web)` | yes | `{}` | `{}` |
| 4 | `invoke_complete(search-web)` | yes | `{}` | `{}` |
| 5 | `invoke_start(summarize)` | yes | `{}` | `{}` |
| 6 | `invoke_complete(summarize)` | yes | `{}` | `{}` |
| 7 | `return_endorsed` | yes | `{}` | `{}` |
| 8 | `revoke` | no | -- | `{}` |

**Takeaway**: Endorsed tools + endorsed return = zero taint propagation
through the entire delegation chain. This is the ideal pattern for
isolated tasks: the parent stays clean regardless of how many endorsed
tools the child uses.

---

## Scenario 5: Full Lifecycle with Taint Propagation

> Assistant delegates a child to read from a database. The child acquires
> sensitive taint, returns the data (unendorsed), and the parent inherits
> the taint. The child is then revoked.

**Agents**: `root` -> `assistant` (holds `{db_read}`) -> `data-reader`

```mermaid
sequenceDiagram
    participant A as assistant
    participant P as Protocol
    participant C as data-reader

    A->>P: delegate(assistant, data-reader)
    P-->>C: data-reader active, caps={}

    A->>P: grant_capability(assistant, data-reader, db_read)
    P-->>C: caps={db_read}

    C->>P: invoke_start(data-reader, read-db, inv1)
    Note over P: All checks pass (no taint, no egress on read-db)
    P-->>C: inv1 in-flight

    P->>C: invoke_complete(data-reader, inv1)
    Note over P: not endorsed, conf_floor=sensitive
    Note over P: data-reader taint += {sensitive}

    C->>P: return_unendorsed(data-reader, assistant)
    Note over P: data-reader in-flight={} -- pass
    Note over P: Flow gate: child taint={sensitive}
    Note over P: assistant in-flight={} -- no pairs to check
    Note over P: assistant taint = {} ∪ {sensitive} = {sensitive}
    P-->>A: unbounded result (taint propagated)

    A->>P: revoke(assistant, data-reader)
    Note over P: data-reader deactivated, all state cleaned
```

| Step | Action | data-reader active | data-reader taint | assistant taint |
|------|--------|:-:|:-:|:-:|
| 0 | -- | no | -- | `{}` |
| 1 | `delegate` | yes | `{}` | `{}` |
| 2 | `grant_capability(db_read)` | yes | `{}` | `{}` |
| 3 | `invoke_start(read-db)` | yes | `{}` | `{}` |
| 4 | `invoke_complete(read-db)` | yes | `{sensitive}` | `{}` |
| 5 | `return_unendorsed` | yes | `{sensitive}` | `{sensitive}` |
| 6 | `revoke` | no | -- | `{sensitive}` |

**Takeaway**: `return_unendorsed` is the taint propagation mechanism.
The parent inherits the child's full taint set via set union. This is
conservative but prevents taint laundering: you cannot avoid acquiring
taint by delegating the sensitive read to a child. The data flows up,
and the taint follows it.

Note that after step 6, the assistant carries `{sensitive}` taint
permanently. Any future invocation of a tool with `network_external`
egress will be evaluated against `(sensitive, network_external) = DENY`.
