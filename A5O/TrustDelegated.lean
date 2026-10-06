/-
  The Algorithm of Trust Delegated
  A Lean 4 model of the A⁵O pre-execution gate: one decision function
  (the algorithm) and the theorems proved about it (the trust).

  Scope of this file: a self-contained model of the gate's decision,
  written against the public layer only (appointer pos. 4, agent pos. 6,
  onebehalfof pos. 7, appointment_ref, revocation_as_of). It does not
  restate or replace the private A⁵O necessity formalization; it states
  what an appointment-bound gate must guarantee, and proves this one does.
  Core Lean 4 only; no external libraries.
-/

namespace A5O.TrustDelegated

/-- A standing appointment (a grant) on the ledger. -/
structure Grant where
  id        : Nat           -- appointment_ref
  appointer : String        -- receipt position 4
  agent     : String        -- receipt position 6
  principal : String        -- receipt position 7 (onebehalfof)
  scope     : List String   -- actions the appointment permits
  deriving DecidableEq, Repr

/-- A request to act, arriving at the gate before execution. -/
structure Request where
  grantRef  : Nat
  agent     : String
  principal : String
  action    : String
  deriving DecidableEq, Repr

/-- The ledger as of the moment before execution (revocation_as_of). -/
structure Ledger where
  grants  : List Grant
  revoked : List Nat
  deriving Repr

inductive Reason where
  | noGrant | revoked | agentMismatch | principalMismatch | outOfScope
  deriving DecidableEq, Repr

inductive Verdict where
  | allow
  | deny (r : Reason)
  deriving DecidableEq, Repr

/-! ## The algorithm -/

/-- The gate. Deny by default; ALLOW only when every check passes. -/
def decide (L : Ledger) (r : Request) : Verdict :=
  match L.grants.find? (fun g => g.id == r.grantRef) with
  | none => .deny .noGrant
  | some g =>
    if r.grantRef ∈ L.revoked then .deny .revoked
    else if g.agent ≠ r.agent then .deny .agentMismatch
    else if g.principal ≠ r.principal then .deny .principalMismatch
    else if r.action ∉ g.scope then .deny .outOfScope
    else .allow

/-! ## The condition the gate must enforce -/

/-- `Appointed L r`: a standing, unrevoked appointment on the ledger names
    this agent, on behalf of this principal, for this action. -/
def Appointed (L : Ledger) (r : Request) : Prop :=
  ∃ g, g ∈ L.grants ∧ g.id = r.grantRef ∧ r.grantRef ∉ L.revoked ∧
       g.agent = r.agent ∧ g.principal = r.principal ∧ r.action ∈ g.scope

/-! ## The trust: theorems about the algorithm -/

/-- Soundness. Every ALLOW is backed by an appointment. -/
theorem soundness (L : Ledger) (r : Request) (h : decide L r = .allow) :
    Appointed L r := by
  unfold decide at h
  split at h
  · cases h
  · rename_i g hfind
    have hmem : g ∈ L.grants := List.mem_of_find?_eq_some hfind
    have hid : (fun g : Grant => g.id == r.grantRef) g = true :=
      List.find?_some (p := fun g : Grant => g.id == r.grantRef) hfind
    by_cases hrev : r.grantRef ∈ L.revoked
    · simp [hrev] at h
    · by_cases ha : g.agent = r.agent
      · by_cases hp : g.principal = r.principal
        · by_cases hs : r.action ∈ g.scope
          · exact ⟨g, hmem, by simpa using hid, hrev, ha, hp, hs⟩
          · simp [hrev, ha, hp, hs] at h
        · simp [hrev, ha, hp] at h
      · simp [hrev, ha] at h

/-- Fail-closed. Without an appointment, the gate never allows. -/
theorem fail_closed (L : Ledger) (r : Request) (h : ¬ Appointed L r) :
    decide L r ≠ .allow := fun ha => h (soundness L r ha)

/-- No grant on the ledger: the verdict is DENY with reason noGrant. -/
theorem deny_no_grant (L : Ledger) (r : Request)
    (h : ∀ g ∈ L.grants, g.id ≠ r.grantRef) :
    decide L r = .deny .noGrant := by
  unfold decide
  have : L.grants.find? (fun g => g.id == r.grantRef) = none := by
    rw [List.find?_eq_none]
    intro g hg
    simpa using h g hg
  rw [this]

/-- A revoked appointment can never produce ALLOW. -/
theorem revoked_never_allows (L : Ledger) (r : Request)
    (h : r.grantRef ∈ L.revoked) : decide L r ≠ .allow := by
  apply fail_closed
  rintro ⟨_, _, _, hrev, _⟩
  exact hrev h

/-- An action outside every matching appointment's scope can never be allowed. -/
theorem out_of_scope_never_allows (L : Ledger) (r : Request)
    (h : ∀ g ∈ L.grants, g.id = r.grantRef → r.action ∉ g.scope) :
    decide L r ≠ .allow := by
  apply fail_closed
  rintro ⟨g, hg, hid, _, _, _, hs⟩
  exact h g hg hid hs

/-- One behalf. An ALLOW is always on behalf of the principal the
    appointment names: the principal cannot be substituted at the gate. -/
theorem allow_preserves_principal (L : Ledger) (r : Request)
    (h : decide L r = .allow) :
    ∃ g, g ∈ L.grants ∧ g.id = r.grantRef ∧ g.principal = r.principal := by
  obtain ⟨g, hg, hid, _, _, hp, _⟩ := soundness L r h
  exact ⟨g, hg, hid, hp⟩

/-- Revocation never creates authority: adding revocations can only
    remove appointments, never add them. -/
theorem revocation_monotone (L L' : Ledger) (r : Request)
    (hg : L'.grants = L.grants)
    (hrev : ∀ x, x ∈ L.revoked → x ∈ L'.revoked)
    (h : Appointed L' r) : Appointed L r := by
  obtain ⟨g, hmem, hid, hnr, ha, hp, hs⟩ := h
  exact ⟨g, hg ▸ hmem, hid, fun hin => hnr (hrev _ hin), ha, hp, hs⟩

/-- Determinism. Same ledger, same request, same verdict: anyone who
    reruns the gate on the same inputs reaches the same answer. -/
theorem deterministic (L : Ledger) (r : Request) (v₁ v₂ : Verdict)
    (h₁ : decide L r = v₁) (h₂ : decide L r = v₂) : v₁ = v₂ :=
  h₁ ▸ h₂

/-! ## Multi-hop: position 4 moves, position 7 holds -/

/-- A sub-appointment: the agent of `g₁` appoints `g₂`, on behalf of the
    same principal, with scope no wider than its own. -/
def Hop (g₁ g₂ : Grant) : Prop :=
  g₂.appointer = g₁.agent ∧ g₂.principal = g₁.principal ∧
  ∀ a, a ∈ g₂.scope → a ∈ g₁.scope

/-- A well-formed delegation chain. -/
def ChainOK : List Grant → Prop
  | [] => True
  | [_] => True
  | g₁ :: g₂ :: rest => Hop g₁ g₂ ∧ ChainOK (g₂ :: rest)

/-- In any well-formed chain, every link acts on behalf of the root
    principal, and no link's scope exceeds the root's. Delegation can
    grow at position 4; it cannot spread at position 7. -/
theorem chain_one_behalf :
    ∀ (rest : List Grant) (root : Grant), ChainOK (root :: rest) →
      ∀ g, g ∈ root :: rest →
        g.principal = root.principal ∧ (∀ a, a ∈ g.scope → a ∈ root.scope)
  | [], root, _, g, hg => by
      simp at hg
      subst hg
      exact ⟨rfl, fun _ h => h⟩
  | g₂ :: rest, root, hc, g, hg => by
      obtain ⟨⟨_, hp, hs⟩, hc'⟩ := hc
      rcases List.mem_cons.mp hg with h | h
      · subst h
        exact ⟨rfl, fun _ h => h⟩
      · obtain ⟨hp', hs'⟩ := chain_one_behalf rest g₂ hc' g h
        exact ⟨hp'.trans hp, fun a ha => hs a (hs' a ha)⟩

/-- Any ALLOW under any link of a well-formed chain is on behalf of the
    root principal and within the root's scope. -/
theorem chain_allow_one_behalf (L : Ledger) (r : Request)
    (root : Grant) (rest : List Grant) (hc : ChainOK (root :: rest))
    (g : Grant) (hgc : g ∈ root :: rest) (hgl : g ∈ L.grants)
    (hid : g.id = r.grantRef) (hunique : ∀ g', g' ∈ L.grants → g'.id = r.grantRef → g' = g)
    (h : decide L r = .allow) :
    r.principal = root.principal ∧ r.action ∈ root.scope := by
  obtain ⟨g', hg', hid', _, _, hp, hs⟩ := soundness L r h
  have hgg : g' = g := hunique g' hg' hid'
  subst hgg
  obtain ⟨hpr, hsc⟩ := chain_one_behalf rest root hc g' hgc
  exact ⟨hp ▸ hpr, hsc _ hs⟩

/-! ## A worked example the kernel evaluates -/

def demoGrant : Grant :=
  { id := 1, appointer := "did:a5o:appointer:agent-obo-inc",
    agent := "did:a5o:agent:iris-01",
    principal := "did:a5o:principal:visionary-member-0710",
    scope := ["book_private_aviation"] }

def demoLedger : Ledger := { grants := [demoGrant], revoked := [] }

def demoRequest : Request :=
  { grantRef := 1, agent := "did:a5o:agent:iris-01",
    principal := "did:a5o:principal:visionary-member-0710",
    action := "book_private_aviation" }

example : decide demoLedger demoRequest = .allow := by native_decide
example : decide demoLedger { demoRequest with action := "wire_funds" }
    = .deny .outOfScope := by native_decide
example : decide { demoLedger with revoked := [1] } demoRequest
    = .deny .revoked := by native_decide
example : decide demoLedger { demoRequest with principal := "did:a5o:principal:other" }
    = .deny .principalMismatch := by native_decide

end A5O.TrustDelegated
