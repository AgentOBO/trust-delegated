# The Algorithm of Trust Delegated

**A Lean 4 formalization of the A⁵O pre-execution gate**
AgentOBO Inc. · Instrument No. A5O-TD-2026-10-06-0001 · Dated 6 October 2026

One decision function — **the algorithm** — and the theorems the Lean kernel has checked about it — **the trust**. The gate denies by default and returns ALLOW only when a standing, unrevoked appointment on the ledger names the requesting agent, on behalf of the named principal, for the requested action.

The model is written against the published layer of the A⁵O receipt: appointer (position 4), agent (position 6), onebehalfof (position 7), appointment_ref, revocation_as_of.

## Theorems

| Theorem | Guarantee |
|---|---|
| `soundness` | Every ALLOW is backed by a standing, unrevoked appointment. |
| `fail_closed` | Without an appointment, the gate never allows. |
| `deny_no_grant` | No grant on the ledger yields DENY, reason noGrant. |
| `revoked_never_allows` | A revoked appointment can never produce ALLOW. |
| `out_of_scope_never_allows` | An action outside scope can never be allowed. |
| `allow_preserves_principal` | The principal at position 7 cannot be substituted at the gate. |
| `revocation_monotone` | Revocation only removes authority; it never creates it. |
| `deterministic` | The same ledger and request always yield the same verdict. |
| `chain_one_behalf` | In any well-formed delegation chain every link acts for the root principal and within the root scope. Position 4 may move; position 7 holds. |
| `chain_allow_one_behalf` | Any ALLOW under any link of a well-formed chain is on behalf of the root principal and within the root scope. |

Axioms used: only Lean's standard `propext` and `Quot.sound`; `revocation_monotone` uses none. No `sorry`.
`chain_allow_one_behalf` assumes unique appointment identifiers on the ledger (stated in its hypotheses). The four worked examples use `native_decide`; the theorems do not.

## Verify it yourself

```
lake build
```
Toolchain: `leanprover/lean4:v4.34.1` (pinned in `lean-toolchain`). Core Lean only — no external libraries.

```
sha256sum A5O/TrustDelegated.lean
# cf65731df4382cb023354629fae845d0ed03e9f01194c6ffcd92658800a8767e
```

## Record

| Item | SHA-256 |
|---|---|
| `A5O/TrustDelegated.lean` | `cf65731df4382cb023354629fae845d0ed03e9f01194c6ffcd92658800a8767e` |
| `seal/seal-a5o.png` (Seal Type 1, A⁵O) | `506558fbf5c246aae97bead981da0039176ddf2600f7e7a0d7a0c919214ff7a4` |
| Executed instrument A5O-TD-2026-10-06-0001 (signed PDF) | `ec4c64f0e327e00c2fc385194d6dd8bb2571f3892634376085bde3144737ebca` |

Executed for and on behalf of AgentOBO Inc. by its Chairman, Founder & CEO, 6 October 2026, under Seal Type 1.

Bitcoin anchors (OpenTimestamps) for the source and seal are in `anchors/`. Verify with:
```
ots verify -f A5O/TrustDelegated.lean anchors/TrustDelegated.lean.ots
ots verify -f seal/seal-a5o.png anchors/seal-a5o.png.ots
```

Prepared at the direction of the Chairman, Founder & CEO of AgentOBO Inc. Drafted with AI assistance (Claude, Anthropic) operating under the Chairman's appointment. Every theorem is machine-checked.

ONEBEHALFOF™, Appointed Intelligence™ and A⁵O Governance Operator™ are trademarks of AgentOBO Inc.
