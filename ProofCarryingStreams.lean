import Init

/-!
Residual-language laws, proof-carrying-stream soundness, and residual separation
for a total deterministic transition function `step : State → Action → State`
with acceptance predicate `accept : State → Prop`. Streams are finite lists;
an `Action` is an addition in the paper's terminology.

Checkers and liveness tests are arbitrary `Prop`-valued predicates; no decision
procedures are supplied. The paper's quotient construction and finite-state
minimality results are not formalized in this file.
-/

set_option autoImplicit false

universe u v w x

namespace ProofCarryingStreams

/-- Execute a finite stream of actions from a state. -/
def run {State : Type u} {Action : Type v}
    (step : State → Action → State) : State → List Action → State
  | s, [] => s
  | s, a :: as => run step (step s a) as

@[simp] theorem run_nil {State : Type u} {Action : Type v}
    (step : State → Action → State) (s : State) :
    run step s [] = s := rfl

@[simp] theorem run_cons {State : Type u} {Action : Type v}
    (step : State → Action → State) (s : State) (a : Action)
    (as : List Action) :
    run step s (a :: as) = run step (step s a) as := rfl

/-- Executing a concatenated stream is the same as executing its two parts. -/
theorem run_append {State : Type u} {Action : Type v}
    (step : State → Action → State) (s : State)
    (xs ys : List Action) :
    run step s (xs ++ ys) = run step (run step s xs) ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons a xs ih => exact ih (s := step s a)

/-- A state is viable when some finite continuation reaches acceptance. -/
def Viable {State : Type u} {Action : Type v}
    (step : State → Action → State) (accept : State → Prop)
    (s : State) : Prop :=
  ∃ w : List Action, accept (run step s w)

/--
The canonical residual at `s`: a stream `u` belongs to it exactly when `u`
can still be extended by some finite suffix to an accepting state.
-/
def Residual {State : Type u} {Action : Type v}
    (step : State → Action → State) (accept : State → Prop)
    (s : State) (u : List Action) : Prop :=
  ∃ v : List Action, accept (run step s (u ++ v))

/-- Viability is membership of the empty stream in the residual. -/
theorem viable_iff_nil_residual {State : Type u} {Action : Type v}
    (step : State → Action → State) (accept : State → Prop)
    (s : State) :
    Viable step accept s ↔ Residual step accept s [] :=
  Iff.rfl

/-- A stream is residual-admissible exactly when its successor state is viable. -/
theorem residual_iff_viable_after_run {State : Type u} {Action : Type v}
    (step : State → Action → State) (accept : State → Prop)
    (s : State) (w : List Action) :
    Residual step accept s w ↔ Viable step accept (run step s w) := by
  unfold Residual Viable
  constructor
  · intro h
    obtain ⟨v, hv⟩ := h
    refine ⟨v, ?_⟩
    rw [← run_append step s w v]
    exact hv
  · intro h
    obtain ⟨v, hv⟩ := h
    refine ⟨v, ?_⟩
    rw [run_append step s w v]
    exact hv

/-- A single action is residually admissible exactly when its successor is viable. -/
theorem canonical_admission_exact {State : Type u} {Action : Type v}
    (step : State → Action → State) (accept : State → Prop)
    (s : State) (a : Action) :
    Residual step accept s [a] ↔ Viable step accept (step s a) :=
  residual_iff_viable_after_run step accept s [a]

/-- The residual after consuming `w` is the left derivative by `w`. -/
theorem residual_after_run_iff {State : Type u} {Action : Type v}
    (step : State → Action → State) (accept : State → Prop)
    (s : State) (w u : List Action) :
    Residual step accept (run step s w) u ↔
      Residual step accept s (w ++ u) := by
  unfold Residual
  constructor
  · intro h
    obtain ⟨v, hv⟩ := h
    refine ⟨v, ?_⟩
    rw [List.append_assoc, run_append]
    exact hv
  · intro h
    obtain ⟨v, hv⟩ := h
    refine ⟨v, ?_⟩
    rw [← run_append step s w (u ++ v), ← List.append_assoc]
    exact hv

/-- A language derivative, included to state the update semantics explicitly. -/
def derivative {Action : Type v}
    (L : List Action → Prop) (w : List Action) : List Action → Prop :=
  fun u => L (w ++ u)

/-- Pointwise form of the canonical derivative identity. -/
theorem residual_derivative {State : Type u} {Action : Type v}
    (step : State → Action → State) (accept : State → Prop)
    (s : State) (w u : List Action) :
    Residual step accept (run step s w) u ↔
      derivative (Residual step accept s) w u :=
  residual_after_run_iff step accept s w u

/-- Compatibility name for the core list-prefix predicate. -/
abbrev IsPrefix {Action : Type v} (p w : List Action) : Prop :=
  List.IsPrefix p w

/-- The canonical residual is prefix closed. -/
theorem residual_prefix_closed {State : Type u} {Action : Type v}
    (step : State → Action → State) (accept : State → Prop)
    (s : State) {p w : List Action}
    (hp : List.IsPrefix p w) (hw : Residual step accept s w) :
    Residual step accept s p := by
  obtain ⟨suffix, hpw⟩ := hp
  obtain ⟨v, hv⟩ := hw
  refine ⟨suffix ++ v, ?_⟩
  rw [← List.append_assoc, hpw]
  exact hv

/-- Every state reached at a prefix of a residual-admissible stream is viable. -/
theorem viable_at_every_prefix {State : Type u} {Action : Type v}
    (step : State → Action → State) (accept : State → Prop)
    (s : State) {p w : List Action}
    (hp : List.IsPrefix p w) (hw : Residual step accept s w) :
    Viable step accept (run step s p) :=
  (residual_iff_viable_after_run step accept s p).mp
    (residual_prefix_closed step accept s hp hw)

/-- Two states are residual-equivalent when they have the same viable continuations. -/
def ResidualEq {State : Type u} {Action : Type v}
    (step : State → Action → State) (accept : State → Prop)
    (s t : State) : Prop :=
  ∀ w : List Action,
    Residual step accept s w ↔ Residual step accept t w

/-- Every state is residual-equivalent to itself. -/
theorem residualEq_refl {State : Type u} {Action : Type v}
    (step : State → Action → State) (accept : State → Prop) (s : State) :
    ResidualEq step accept s s :=
  fun _ => Iff.rfl

/-- Residual equivalence is symmetric. -/
theorem residualEq_symm {State : Type u} {Action : Type v}
    (step : State → Action → State) (accept : State → Prop)
    {s t : State} (h : ResidualEq step accept s t) :
    ResidualEq step accept t s :=
  fun stream => (h stream).symm

/-- Residual equivalence is transitive. -/
theorem residualEq_trans {State : Type u} {Action : Type v}
    (step : State → Action → State) (accept : State → Prop)
    {s t r : State} (hst : ResidualEq step accept s t)
    (htr : ResidualEq step accept t r) :
    ResidualEq step accept s r :=
  fun stream => (hst stream).trans (htr stream)

/-- Residual-equivalent states agree on viability. -/
theorem residualEq_viable {State : Type u} {Action : Type v}
    (step : State → Action → State) (accept : State → Prop)
    {s t : State} (h : ResidualEq step accept s t) :
    Viable step accept s ↔ Viable step accept t :=
  (viable_iff_nil_residual step accept s).trans
    ((h []).trans (viable_iff_nil_residual step accept t).symm)

/-- Canonical one-step update of a residual language. -/
def residualUpdate {Action : Type v}
    (L : List Action → Prop) (a : Action) : List Action → Prop :=
  fun w => L (a :: w)

/-- The canonical residual update is exact. -/
theorem canonical_update_exact {State : Type u} {Action : Type v}
    (step : State → Action → State) (accept : State → Prop)
    (s : State) (a : Action) (w : List Action) :
    Residual step accept (step s a) w ↔
      residualUpdate (Residual step accept s) a w :=
  residual_after_run_iff step accept s [a] w

/-- Equality form of `canonical_update_exact`, via `funext` and `propext`. It can
serve as the `hupdate` argument when states are encoded as their residuals. -/
theorem canonical_update_eq {State : Type u} {Action : Type v}
    (step : State → Action → State) (accept : State → Prop)
    (s : State) (a : Action) :
    Residual step accept (step s a) = residualUpdate (Residual step accept s) a := by
  funext stream
  exact propext (canonical_update_exact step accept s a stream)

/-- A certificate is sound at `s` when every stream it denotes belongs to the residual. -/
def CertSoundAt {State : Type u} {Action : Type v} {Cert : Type w}
    (step : State → Action → State) (accept : State → Prop)
    (denote : Cert → List Action → Prop) (s : State) (c : Cert) : Prop :=
  ∀ stream, denote c stream → Residual step accept s stream

/-- A certificate is nonempty when it denotes at least one future stream. -/
def CertNonempty {Action : Type v} {Cert : Type w}
    (denote : Cert → List Action → Prop) (c : Cert) : Prop :=
  ∃ stream, denote c stream

/--
A checker is stepwise sound when every accepted update refines the preceding
certificate by the consumed action and leaves a nonempty successor certificate.
-/
def StepwiseSound {Action : Type v} {Cert : Type w} {Evidence : Type x}
    (denote : Cert → List Action → Prop)
    (check : Cert → Action → Cert → Evidence → Prop) : Prop :=
  ∀ c a c' eta, check c a c' eta →
    (∀ stream, denote c' stream → denote c (a :: stream)) ∧
    CertNonempty denote c'

/-- A sound, nonempty certificate implies viability of its concrete state. -/
theorem cert_sound_nonempty_viable
    {State : Type u} {Action : Type v} {Cert : Type w}
    (step : State → Action → State) (accept : State → Prop)
    (denote : Cert → List Action → Prop) {s : State} {c : Cert}
    (hsound : CertSoundAt step accept denote s c)
    (hnonempty : CertNonempty denote c) :
    Viable step accept s := by
  obtain ⟨stream, hstream⟩ := hnonempty
  obtain ⟨suffix, hsuffix⟩ := hsound stream hstream
  exact ⟨stream ++ suffix, hsuffix⟩

/-- One accepted checker step preserves certificate soundness and nonemptiness. -/
theorem checked_step_preserves_certificate
    {State : Type u} {Action : Type v} {Cert : Type w} {Evidence : Type x}
    (step : State → Action → State) (accept : State → Prop)
    (denote : Cert → List Action → Prop)
    (check : Cert → Action → Cert → Evidence → Prop)
    (hstepwise : StepwiseSound denote check)
    {s : State} {c c' : Cert} {a : Action} {eta : Evidence}
    (hsound : CertSoundAt step accept denote s c)
    (hcheck : check c a c' eta) :
    CertSoundAt step accept denote (step s a) c' ∧
      CertNonempty denote c' := by
  have hlocal := hstepwise c a c' eta hcheck
  constructor
  · intro stream hc'
    have hc : denote c (a :: stream) := hlocal.1 stream hc'
    have hres : Residual step accept s (a :: stream) :=
      hsound (a :: stream) hc
    exact (canonical_update_exact step accept s a stream).mpr hres
  · exact hlocal.2

/-- A proposition certifying a finite chain of checked steps, recording the state
and certificate at every position including the first and last. -/
inductive ProofCarryingStream
    {State : Type u} {Action : Type v} {Cert : Type w} {Evidence : Type x}
    (step : State → Action → State)
    (check : Cert → Action → Cert → Evidence → Prop) :
    State → Cert → List (State × Cert) → Prop where
  /-- The empty stream records only its starting state and certificate. -/
  | nil (s : State) (c : Cert) :
      ProofCarryingStream step check s c [(s, c)]
  /-- An accepted check extends the stream by one action, recording the
  state and certificate before the step. -/
  | cons {s : State} {c c' : Cert} {a : Action} {eta : Evidence}
      {tail : List (State × Cert)}
      (hcheck : check c a c' eta)
      (hrest : ProofCarryingStream step check (step s a) c' tail) :
      ProofCarryingStream step check s c ((s, c) :: tail)

/-- Every element of a list satisfies the given predicate. -/
inductive ListAll {α : Type u} (p : α → Prop) : List α → Prop where
  /-- The empty list satisfies every predicate. -/
  | nil : ListAll p []
  /-- A list satisfies `ListAll p` when its head satisfies `p` and its tail
  satisfies `ListAll p`. -/
  | cons {a : α} {as : List α} : p a → ListAll p as → ListAll p (a :: as)

/--
The machine-checked counterpart of the paper's proof-carrying-stream soundness
theorem: every recorded prefix carries a sound, nonempty certificate and is viable.
-/
theorem proof_carrying_stream_soundness
    {State : Type u} {Action : Type v} {Cert : Type w} {Evidence : Type x}
    (step : State → Action → State) (accept : State → Prop)
    (denote : Cert → List Action → Prop)
    (check : Cert → Action → Cert → Evidence → Prop)
    (hstepwise : StepwiseSound denote check)
    {s : State} {c : Cert} {snapshots : List (State × Cert)}
    (hstream : ProofCarryingStream step check s c snapshots) :
    CertSoundAt step accept denote s c →
    CertNonempty denote c →
    ListAll
      (fun sc =>
        CertSoundAt step accept denote sc.1 sc.2 ∧
        CertNonempty denote sc.2 ∧
        Viable step accept sc.1)
      snapshots := by
  induction hstream with
  | nil s c =>
      intro hsound hnonempty
      have hviable : Viable step accept s :=
        cert_sound_nonempty_viable step accept denote hsound hnonempty
      exact ListAll.cons ⟨hsound, hnonempty, hviable⟩ ListAll.nil
  | cons hcheck hrest ih =>
      intro hsound hnonempty
      have hnext :=
        checked_step_preserves_certificate step accept denote check
          hstepwise hsound hcheck
      have hviable : Viable step accept _ :=
        cert_sound_nonempty_viable step accept denote hsound hnonempty
      exact ListAll.cons
        ⟨hsound, hnonempty, hviable⟩
        (ih hnext.1 hnext.2)

/-- Residual equivalence is preserved by applying the same next action. -/
theorem residualEq_step {State : Type u} {Action : Type v}
    (step : State → Action → State) (accept : State → Prop)
    {s t : State} (h : ResidualEq step accept s t) (a : Action) :
    ResidualEq step accept (step s a) (step t a) := by
  intro w
  calc
    Residual step accept (step s a) w
        ↔ residualUpdate (Residual step accept s) a w :=
          canonical_update_exact step accept s a w
    _ ↔ residualUpdate (Residual step accept t) a w := h (a :: w)
    _ ↔ Residual step accept (step t a) w :=
          (canonical_update_exact step accept t a w).symm

/-- Residual equivalence is preserved by executing any common finite stream. -/
theorem residualEq_run {State : Type u} {Action : Type v}
    (step : State → Action → State) (accept : State → Prop)
    {s t : State} (h : ResidualEq step accept s t) (stream : List Action) :
    ResidualEq step accept (run step s stream) (run step t stream) := by
  intro suffix
  exact (residual_after_run_iff step accept s stream suffix).trans
    ((h (stream ++ suffix)).trans
      (residual_after_run_iff step accept t stream suffix).symm)

/-- Iterate an arbitrary proof-state update over a finite stream.
This is `run` at the proof-state type; it is named separately so that the
paper's statements can refer to it. -/
def updateMany {Action : Type v} {ProofState : Type w}
    (update : ProofState → Action → ProofState) :
    ProofState → List Action → ProofState :=
  run update

/-- One-step exactness of a proof-state encoding lifts to arbitrary streams. -/
theorem encode_run_eq_updateMany
    {State : Type u} {Action : Type v} {ProofState : Type w}
    (step : State → Action → State)
    (encode : State → ProofState) (update : ProofState → Action → ProofState)
    (hupdate : ∀ s a, encode (step s a) = update (encode s) a)
    (s : State) (stream : List Action) :
    encode (run step s stream) =
      updateMany update (encode s) stream := by
  induction stream generalizing s with
  | nil => rfl
  | cons a stream ih =>
      calc
        encode (run step s (a :: stream))
            = encode (run step (step s a) stream) := rfl
        _ = updateMany update (encode (step s a)) stream :=
              ih (s := step s a)
        _ = updateMany update (update (encode s) a) stream := by
              rw [hupdate s a]
        _ = updateMany update (encode s) (a :: stream) := rfl

/--
Residual separation theorem.

If a proof-state abstraction has an exact update and an exact liveness
predicate, then any two concrete states with the same encoding are
residual-equivalent: the abstraction cannot identify states that disagree
about any viable future stream.
-/
theorem exact_proof_state_preserves_residual_distinctions
    {State : Type u} {Action : Type v} {ProofState : Type w}
    (step : State → Action → State) (accept : State → Prop)
    (encode : State → ProofState) (update : ProofState → Action → ProofState)
    (live : ProofState → Prop)
    (hupdate : ∀ s a, encode (step s a) = update (encode s) a)
    (hlive : ∀ s, live (encode s) ↔ Viable step accept s)
    {s t : State} (hst : encode s = encode t) :
    ResidualEq step accept s t := by
  intro stream
  have henc :
      encode (run step s stream) = encode (run step t stream) := by
    calc
      encode (run step s stream)
          = updateMany update (encode s) stream :=
              encode_run_eq_updateMany step encode update hupdate s stream
      _ = updateMany update (encode t) stream := by rw [hst]
      _ = encode (run step t stream) :=
              (encode_run_eq_updateMany step encode update hupdate t stream).symm
  calc
    Residual step accept s stream
        ↔ Viable step accept (run step s stream) :=
          residual_iff_viable_after_run step accept s stream
    _ ↔ live (encode (run step s stream)) :=
          (hlive (run step s stream)).symm
    _ ↔ live (encode (run step t stream)) := by rw [henc]
    _ ↔ Viable step accept (run step t stream) :=
          hlive (run step t stream)
    _ ↔ Residual step accept t stream :=
          (residual_iff_viable_after_run step accept t stream).symm

/-- Liveness of the canonical residual proof state is empty-stream membership. -/
def ResidualLive {Action : Type v} (L : List Action → Prop) : Prop :=
  L []

/-- Compatibility name for `ResidualLive`. -/
abbrev residualLive {Action : Type v} (L : List Action → Prop) : Prop :=
  ResidualLive L

/-- The canonical residual proof state has exact liveness. -/
theorem canonical_live_exact {State : Type u} {Action : Type v}
    (step : State → Action → State) (accept : State → Prop)
    (s : State) :
    ResidualLive (Residual step accept s) ↔ Viable step accept s :=
  (viable_iff_nil_residual step accept s).symm

/--
The canonical residual satisfies pointwise update and exact viability laws via
`residualUpdate` and `ResidualLive`.
-/
theorem canonical_abstraction_is_exact
    {State : Type u} {Action : Type v}
    (step : State → Action → State) (accept : State → Prop) :
    (∀ s a w,
      Residual step accept (step s a) w ↔
        residualUpdate (Residual step accept s) a w) ∧
    (∀ s, ResidualLive (Residual step accept s) ↔
      Viable step accept s) :=
  ⟨fun s a w => canonical_update_exact step accept s a w,
   fun s => canonical_live_exact step accept s⟩

end ProofCarryingStreams

#print axioms ProofCarryingStreams.proof_carrying_stream_soundness
#print axioms ProofCarryingStreams.exact_proof_state_preserves_residual_distinctions
#print axioms ProofCarryingStreams.canonical_abstraction_is_exact
#print axioms ProofCarryingStreams.canonical_update_eq
