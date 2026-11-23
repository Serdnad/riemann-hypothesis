module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CyclotomicInertiaSpan.DecComm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.PowOneInj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RootsOfUnityShapes.ConjFlag
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RootsOfUnityShapes.DiagGsp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RootsOfUnityShapes.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RootsOfUnityShapes.PowIne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RootsOfUnityShapes.ShapeQ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.BigOm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.MkTower
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

local instance (priority := 2000) ratFieldIsTorsionFreeForCompactIntegralFieldsBundle005 (Ω : Type) [Field Ω] [CharZero Ω] :
    Module.IsTorsionFree ℚ Ω := DivisionSemiring.to_moduleIsTorsionFree

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem muIne {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (F : IntermediateField ℚ Ω) [NumberField F]
    (l : ℕ) [hl : Fact l.Prime] (A : ValuationSubring Ω) (hA : A.valuation (l : Ω) < 1) {s : G F Ω}
    (hs : s ∈ muOf l (Dec (F := F) A)) : s ∈ Ine (F := F) A := by
  haveI : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed ℚ, inferInstance⟩
  obtain ⟨h1, a, h2⟩ := hs
  exact Rq.powIne F Ω l A hA s h1 _ (pow_pos hl.out.pos a)
    (Subgroup.topologicalClosure_minimal _ (UpperTheory.V.B1.decComm F Ω l A hA) (isClosed_Ine A) h2)

private theorem cont_resQ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (F : IntermediateField ℚ Ω) [NumberField F] :
    Continuous (resQ F) := by
  haveI : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed ℚ, inferInstance⟩
  exact (galEmbTop ℚ F Ω).1.continuous

private theorem low_desc {A V : Type} [CommRing A] [CommRing V] [IsLocalRing V] (f : A →+* V) (hf : Function.Injective f)
    [IsLocalHom f] (ν : V) (hν : IsUnit ν) (X n₀ : M4 A) (hX : IsGSp ν (X.map f)) (h0 : IsLow (n₀.map f))
    (hs : SuppM nP ((X.map f).map (residue V))) (hd : ∀ i, IsUnit (((X.map f).map (residue V)) i i))
    (h0' : IsLow ((n₀.map f).map (residue V))) (hq : SuppM qQ ((n₀.map f).map (residue V))) :
    ∃ n : M4 A, IsLow n ∧ IsUp (adj n * X * n₀) := by
  have hG : ∀ (μ : A) (Y : M4 A), IsGSp (f μ) (Y.map f) → IsGSp μ Y := fun μ Y h => by
    unfold IsGSp at h ⊢
    rw [adj_map, ← Matrix.map_mul] at h
    ext i j
    apply hf
    have := congrFun (congrFun h i) j
    rw [Matrix.map_apply] at this
    rw [this]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hμ : f ((adj X * X) 0 0) = ν := by
    have h := hX
    unfold IsGSp at h
    rw [adj_map, ← Matrix.map_mul] at h
    simpa using congrFun (congrFun h 0) 0
  obtain ⟨⟨u1, u2⟩, -⟩ := Rq.shapeQ _ _ _ hs hd h0' hq
  rw [← Matrix.map_mul, ← Matrix.map_mul] at u1 u2
  simp only [Matrix.map_apply, ← map_mul, ← map_sub] at u1 u2
  refine Rq.luG A ((adj X * X) 0 0) X n₀ (IsUnit.of_map f _ (hμ ▸ hν)) (hG _ _ (hμ ▸ hX))
    ⟨hG 1 _ (by rw [map_one]; exact h0.1), fun i => hf ?_, fun i j hij => hf ?_⟩
    (IsUnit.of_map f _ (IsUnit.of_map (residue V) _ u1)) (IsUnit.of_map f _ (IsUnit.of_map (residue V) _ u2))
  · rw [map_one]; exact h0.2.1 i
  · rw [map_zero]; exact h0.2.2 i j hij

private theorem low_map {A V : Type} [CommRing A] [CommRing V] (f : A →+* V) {n : M4 A} (h : IsLow n) : IsLow (n.map f) :=
  ⟨by simpa using isGSp_map f h.1, fun i => by rw [Matrix.map_apply, h.2.1, map_one],
    fun i j hij => by rw [Matrix.map_apply, h.2.2 i j hij, map_zero]⟩

private theorem up_map {A V : Type} [CommRing A] [CommRing V] (f : A →+* V) {n X m : M4 A} (h : IsUp (adj n * X * m)) :
    IsUp (adj (n.map f) * X.map f * m.map f) := fun i j hij => by
  rw [adj_map, ← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_apply, h i j hij, map_zero]

theorem UpperTheory.V.Ws.restrQ :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ T₀ T : Tower D, T₀.Fit → T₀.Le T → ∀ (𝔞 : Amb l) (P : PD Unit (G ℚ Ω) 𝔞.V), QPair D T₀.pr (resQ T₀.F T₀.g0) 𝔞 P →
      LatShape D T₀.pr (resQ T₀.F T₀.g0) (𝔞.red c) (P.map (residue 𝔞.V)) →
      ∃ P' : PD T.ι (G T.F Ω) 𝔞.V, 𝔞.Small P' ∧ (T.fr ∅).IsPair (𝔞.a c) P' ∧ P'.r = P.r.comp (resQ T.F) ∧
        T.OverQ (P.map (residue 𝔞.V)) (P'.map (residue 𝔞.V)) ∧ (T.fr ∅).IsRes (𝔞.red c) (P'.map (residue 𝔞.V)) ∧
        ∀ v i, ∀ s ∈ Ine (F := T.F) (T.pl v), P'.ψ v i s = 𝔞.a c (D.ps i (resQ T.F s)) := by
  intro Ω _ _ _ l hl c D hD T₀ T hF hLe 𝔞 P hP hS
  have hOk : T.Ok := (leFit D hD T₀ T hLe).1 hF.1
  obtain ⟨A, _, _, _, f, P₁, hf, hc, rfl⟩ := hP.small
  haveI := hf.loc
  choose g hg hgD hgI using fun v : T.ι => Rq.placeMove T.F l hl.out (T.pl v) (D.pl l) (T.ovl v) (hD.pl_over l hl.out)
  have hν : ∀ x, IsUnit (𝔞.a c (D.th x)) := fun x => (D.th x).isUnit.map _
  have hd : ∀ x i, IsUnit ((((P₁.map f).map (residue 𝔞.V)).r x) i i) := fun x i => by
    rw [hS.res.res.diag]
    exact (Units.isUnit _).map _
  choose n hn hb using fun v : T.ι => low_desc f hf.inj _ (hν (g v)) (P₁.r (g v)) (P₁.n ()) (hP.pair.mult (g v))
    (hP.pair.low ()) (hS.supp (g v)) (hd (g v)) (hS.res.pair.low ()) hS.flag
  let Q : PD T.ι (G T.F Ω) A := ⟨P₁.r.comp (resQ T.F), n⟩
  have key : ∀ v, ∀ s ∈ Dec (F := T.F) (T.pl v), IsUp (adj ((Q.map f).n v) * (Q.map f).r s * (Q.map f).n v) ∧
      ∀ i, (Q.map f).ψ v i s = (P₁.map f).ψ () i ((g v)⁻¹ * resQ T.F s * g v) := fun v s hs =>
    Rq.conjFlag _ _ ((P₁.map f).r (g v)) ((P₁.map f).r ((g v)⁻¹ * resQ T.F s * g v)) ((P₁.map f).r (resQ T.F s)) _ _
      (hν (g v)) (hP.pair.mult (g v)) (hP.pair.low ()) (low_map f (hn v)) (up_map f (hb v))
      (by rw [← map_mul, ← map_mul, mul_assoc, mul_inv_cancel_left]) (hP.pair.flag () _ (hgD v s hs))
  have hconj : ∀ (χ : G ℚ Ω →* c.Oˣ) (x y : G ℚ Ω), χ (x⁻¹ * y * x) = χ y := fun χ x y => by
    rw [map_mul, map_mul, map_inv, mul_comm, mul_inv_cancel_left]
  have hI : ∀ v i, ∀ s ∈ Ine (F := T.F) (T.pl v), (Q.map f).ψ v i s = 𝔞.a c (D.ps i (resQ T.F s)) := fun v i s hs => by
    rw [(key v s (Ine_le_Dec _ hs)).2, hP.inert _ (hgI v s hs), hconj]
  have hpair : (T.fr ∅).IsPair (𝔞.a c) (Q.map f) := by
    refine ⟨fun x => hP.pair.mult (resQ T.F x), Rq.killQ D hD T hOk _ _ _ (P₁.map f).r hP.pair.kill, ?_,
      fun v => low_map f (hn v), fun v s hs => (key v s hs).1, fun v s hs i => ?_⟩
    · obtain ⟨j, hj⟩ := hLe.g0
      show ((P₁.map f).r (resQ T.F T.g0)).IsDiag
      have h := hP.pair.nrm
      change ((P₁.map f).r (resQ T₀.F T₀.g0)).IsDiag at h
      rw [hj, map_pow, ← h.diagonal_diag, Matrix.diagonal_pow]
      exact Matrix.isDiag_diagonal _
    · refine (hI v i s (muIne T.F l _ (T.ovl v) hs)).trans ?_
      rw [Rq.muPs D hD T hOk _ s hs i, Units.val_one, map_one]
  have hb' : ∀ v, IsUp (adj (((Q.map f).map (residue 𝔞.V)).n v) * ((P₁.map f).map (residue 𝔞.V)).r (g v) *
      ((P₁.map f).map (residue 𝔞.V)).n ()) := fun v => up_map (residue 𝔞.V) (up_map f (hb v))
  have hp' := hpair.map (residue 𝔞.V)
  refine ⟨Q.map f, ⟨A, _, _, inferInstance, f, Q, hf, fun i j N => (hc i j N).comp_continuous (cont_resQ T.F), rfl⟩, hpair, rfl,
    ⟨rfl, fun v => ⟨(), g v, hg v, hb' v⟩⟩, ⟨hp', ⟨fun x i => ?_, fun v s hs i => ?_, Or.inl ⟨fun x => hS.supp _, fun v => ?_⟩⟩,
      fun i j N => (hS.res.cont i j N).comp_continuous (cont_resQ T.F)⟩, hI⟩
  · show _ = 𝔞.red c (chi D T.pr i (resQ T.F x))
    rw [hLe.pr]
    exact hS.res.res.diag (resQ T.F x) i
  · show _ = 𝔞.red c (chi D T.pr i (resQ T.F s))
    refine (PD.map_ψ (Q.map f) (residue 𝔞.V) v i s).trans ?_
    rw [(key v s hs).2, ← PD.map_ψ, hLe.pr, ← hconj (chi D T₀.pr i) (g v)]
    exact hS.res.res.char () _ (hgD v s hs) i
  · exact (Rq.shapeQ _ _ _ (hS.supp (g v)) (hd (g v)) (hS.res.pair.low ()) hS.flag).2 _ (hp'.low v) (hb' v)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.exists_tame_tower_ok_two :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), Ctx2 D → ∀ pr, LabOk D pr → ∃ T : Tower D, T.pr = pr ∧ T.Ok ∧ T.Two ∧ TameL l T.F := by
  intro Ω _ _ _ l _ c D hC pr hpr
  have hD := hC.1
  obtain ⟨κ, hκ⟩ : ∃ κ, Kap D κ := by
    obtain ⟨-, h, t, e, ψ, -, -, -, -, -, hO⟩ := hC
    exact kapEx D hD h.N ψ hO.psi
  obtain ⟨j, hj⟩ := hκ.pow
  obtain ⟨p₃, φ, hφ⟩ := quadEx Ω 1 D.S hD.S_prime
  have h1 : ∀ q ∈ insert p₃ D.S, q.Prime := Finset.forall_mem_insert _ _ _ |>.2 ⟨hφ.prime, hD.S_prime⟩
  obtain ⟨p, η, hη⟩ := quadEx Ω (-1) _ h1
  obtain ⟨p', η', hη'⟩ := quadEx Ω (-1) (insert p (insert p₃ D.S)) (Finset.forall_mem_insert _ _ _ |>.2 ⟨hη.prime, h1⟩)
  obtain ⟨x1, x2, x3⟩ := xi2 D hC
  let X : Set2 D := ⟨κ, p₃, p, p', φ, η, η', hκ, hφ, hη, hη', x3, x1, x2, ev2 D hC κ j hj, exists_decomposition_element_at_l_xi_pow_four_ne_one D hC κ j hj, exists_inertia_element_at_two_xi_pow_four_ne_one D hC κ j hj⟩
  obtain ⟨b1, b2, b3, b4, b5⟩ := characterSubgroup_open_even_index_tame_power D hD X
  obtain ⟨F, _, _, hF, dF⟩ := fixAb Ω X.H b1 b2
  obtain ⟨K, _, _, hK, dK⟩ := fixAb Ω η.ker hη.opn (Abelianization.commutator_subset_ker η)
  obtain ⟨k₀, _, _, hk, dk⟩ := fixAb Ω φ.ker hφ.opn (Abelianization.commutator_subset_ker φ)
  rw [hη.idx] at dK
  rw [hφ.idx] at dk
  haveI : IsTotallyReal F := (fixInf Ω F).1 (hF ▸ b3)
  haveI : IsCMField K := (fixInf Ω K).2 (fun σ hσ h => by
    rw [hK, MonoidHom.mem_ker, hη.cc σ hσ] at h
    exact absurd h (by decide)) dK
  have rk : IsTotallyReal k₀ := (fixInf Ω k₀).1 fun σ hσ => hk ▸ hφ.cc σ hσ
  have sp : ∀ q ∈ D.S, ∀ A : ValuationSubring Ω, A.valuation (q : Ω) < 1 → Dec (F := ℚ) A ≤ K.fixingSubgroup :=
    fun q hq A hA => hK ▸ hη.split q (Finset.mem_insert_of_mem hq) A hA
  obtain ⟨a, u, t, hE⟩ := elts2 D hD X
  obtain ⟨g0, hg0⟩ := exists_resQ (F := F) (g := t) (hF ▸ hE.t_mem.1)
  obtain ⟨T, e1, e2, e3, e4⟩ := mkTower D hD pr K F dK (sp l hD.l_mem) g0
  have hT : X.On T := ⟨e3 ▸ hF, e2 ▸ hK⟩
  obtain ⟨a1, a2, a3, a4, a5⟩ := ok2A D hD X T hT a u t hE
  obtain ⟨c1, c2, c3, c4⟩ := ok2B D hD X T hT
  have ev : Even T.d := by
    rw [Tower.d, IntermediateField.finrank_eq_fixingSubgroup_index, hT.1]
    exact b4
  exact ⟨T, e1, ⟨e1 ▸ hpr, ev, c1, e2 ▸ sp, a1, a2, a3, a4, c2, c3, c4, a5 (e4.trans hg0), UpperTheory.V.Keep.loc2 D hC X T hT⟩,
    two2 D hD X T hT k₀ dk rk hk, fun A hA g hg => hT.1 ▸ b5 A hA g hg⟩
end
