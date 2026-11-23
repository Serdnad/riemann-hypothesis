module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.SimpleIn
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

section

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.HopfProductGluing

private def dbl {G : Type} [Group G] (U : Subgroup G) (g : G) : Set (G ⧸ U) :=
  {c : G ⧸ U | ∃ u ∈ U, c = QuotientGroup.mk (u * g)}

private theorem dbl_finite {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {U : Subgroup G}
    (hU : CO U) (g : G) : (dbl U g).Finite := by
  haveI : DiscreteTopology (G ⧸ U) := QuotientGroup.discreteTopology hU.2
  have hc : Continuous fun u : G => (QuotientGroup.mk (u * g) : G ⧸ U) :=
    QuotientGroup.continuous_mk.comp (continuous_id.mul continuous_const)
  refine ((hU.1.image hc).finite_of_discrete).subset ?_
  rintro c ⟨u, hu, rfl⟩
  exact ⟨u, hu, rfl⟩

private theorem act_congr {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    {U : Subgroup G} {v : V} (hv : ∀ u ∈ U, ρ u v = v) {x y : G}
    (h : (QuotientGroup.mk x : G ⧸ U) = QuotientGroup.mk y) : ρ x v = ρ y v := by
  have h1 := hv _ (QuotientGroup.eq.1 h)
  calc ρ x v = ρ x (ρ (x⁻¹ * y) v) := by rw [h1]
    _ = ρ y v := by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]

variable {r : ℕ} {G : Fin r → Type} [∀ i, Group (G i)]

private theorem mk_eq (U : ∀ i, Subgroup (G i)) (x y : ∀ i, G i) :
    (QuotientGroup.mk x : (∀ i, G i) ⧸ Subgroup.pi Set.univ U) = QuotientGroup.mk y ↔
      ∀ j, (QuotientGroup.mk (x j) : G j ⧸ U j) = QuotientGroup.mk (y j) := by
  simp [QuotientGroup.eq, Subgroup.mem_pi]

private noncomputable def pr (U : ∀ i, Subgroup (G i)) (j : Fin r) (c : (∀ i, G i) ⧸ Subgroup.pi Set.univ U) : G j ⧸ U j :=
  QuotientGroup.mk (c.out j)

private theorem pr_mk (U : ∀ i, Subgroup (G i)) (j : Fin r) (x : ∀ i, G i) :
    pr U j (QuotientGroup.mk x) = QuotientGroup.mk (x j) :=
  (mk_eq U _ _).1 (QuotientGroup.out_eq' _) j

private theorem pr_ext (U : ∀ i, Subgroup (G i)) {c d : (∀ i, G i) ⧸ Subgroup.pi Set.univ U}
    (h : ∀ j, pr U j c = pr U j d) : c = d := by
  rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' d]
  exact (mk_eq U _ _).2 h

private theorem mem_dbl (U : ∀ i, Subgroup (G i)) (g : ∀ i, G i) (c : (∀ i, G i) ⧸ Subgroup.pi Set.univ U) :
    c ∈ dbl (Subgroup.pi Set.univ U) g ↔ ∀ j, pr U j c ∈ dbl (U j) (g j) := by
  constructor
  · rintro ⟨u, hu, rfl⟩ j
    exact ⟨u j, hu j trivial, pr_mk U j _⟩
  · intro h
    choose u hu he using h
    exact ⟨u, fun j _ => hu j, pr_ext U fun j => by rw [pr_mk]; exact he j⟩

private theorem mem_dbl_one {H : Type} [Group H] (U : Subgroup H) (c : H ⧸ U) :
    c ∈ dbl U 1 ↔ c = QuotientGroup.mk 1 := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa [QuotientGroup.eq] using hu
  · rintro rfl
    exact ⟨1, U.one_mem, by simp⟩

private noncomputable def glue (U : ∀ i, Subgroup (G i)) (i : Fin r) (c d : (∀ i, G i) ⧸ Subgroup.pi Set.univ U) :
    (∀ i, G i) ⧸ Subgroup.pi Set.univ U :=
  QuotientGroup.mk (Pi.mulSingle i (c.out i) * d.out)

private theorem pr_glue_same (U : ∀ i, Subgroup (G i)) (i : Fin r) (c d : (∀ i, G i) ⧸ Subgroup.pi Set.univ U)
    (hd : pr U i d = QuotientGroup.mk 1) : pr U i (glue U i c d) = pr U i c := by
  rw [glue, pr_mk]
  have := QuotientGroup.eq.1 hd
  simpa [pr, QuotientGroup.eq] using this

private theorem pr_glue_ne (U : ∀ i, Subgroup (G i)) {i j : Fin r} (h : j ≠ i)
    (c d : (∀ i, G i) ⧸ Subgroup.pi Set.univ U) : pr U j (glue U i c d) = pr U j d := by
  rw [glue, pr_mk]
  simp [pr, Pi.mulSingle_eq_of_ne h]

private theorem hop_mul [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)] {V : Type} [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ (∀ i, G i) V) (U : ∀ i, Subgroup (G i)) (hU : ∀ i, CO (U i))
    (i : Fin r) (x : G i) (b : ∀ i, G i) (hb : b i = 1) (v : V) (hv : ∀ u ∈ Subgroup.pi Set.univ U, ρ u v = v)
    (hw : ∀ u ∈ Subgroup.pi Set.univ U, ρ u (hopR ρ (Subgroup.pi Set.univ U) b v) = hopR ρ (Subgroup.pi Set.univ U) b v) :
    hopR ρ (Subgroup.pi Set.univ U) (Pi.mulSingle i x * b) v =
      hopR ρ (Subgroup.pi Set.univ U) (Pi.mulSingle i x) (hopR ρ (Subgroup.pi Set.univ U) b v) := by
  have hW : CO (Subgroup.pi Set.univ U) :=
    ⟨isCompact_univ_pi fun j => (hU j).1, isOpen_set_pi Set.finite_univ fun j _ => (hU j).2⟩
  have hs : ∀ g w, hopR ρ (Subgroup.pi Set.univ U) g w = ∑ c ∈ (dbl_finite hW g).toFinset, ρ c.out w :=
    fun g w => finsum_mem_eq_finite_toFinset_sum _ (dbl_finite hW g)
  have ha : ∀ c ∈ dbl (Subgroup.pi Set.univ U) (Pi.mulSingle i x), ∀ j, j ≠ i → pr U j c = QuotientGroup.mk 1 := by
    intro c hc j hj
    have := (mem_dbl U _ c).1 hc j
    rwa [Pi.mulSingle_eq_of_ne hj, mem_dbl_one] at this
  have hb' : ∀ d ∈ dbl (Subgroup.pi Set.univ U) b, pr U i d = QuotientGroup.mk 1 := by
    intro d hd
    have := (mem_dbl U _ d).1 hd i
    rwa [hb, mem_dbl_one] at this
  have h1 : hopR ρ (Subgroup.pi Set.univ U) (Pi.mulSingle i x) (hopR ρ (Subgroup.pi Set.univ U) b v) =
      ∑ p ∈ (dbl_finite hW (Pi.mulSingle i x)).toFinset ×ˢ (dbl_finite hW b).toFinset,
        ρ (glue U i p.1 p.2).out v := by
    rw [hs (Pi.mulSingle i x), Finset.sum_product]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [Set.Finite.mem_toFinset] at hc
    have e : ρ c.out (hopR ρ (Subgroup.pi Set.univ U) b v) =
        ρ (Pi.mulSingle i (c.out i)) (hopR ρ (Subgroup.pi Set.univ U) b v) := by
      refine act_congr ρ hw ((mk_eq U _ _).2 fun j => ?_)
      by_cases hj : j = i
      · subst hj; simp
      · rw [Pi.mulSingle_eq_of_ne hj]; exact ha c hc j hj

    rw [e, hs b, map_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← Module.End.mul_apply, ← map_mul]
    exact act_congr ρ hv (QuotientGroup.out_eq' _).symm
  rw [h1, hs]
  symm
  refine Finset.sum_bij (fun p _ => glue U i p.1 p.2) ?_ ?_ ?_ (fun _ _ => rfl)
  · rintro ⟨c, d⟩ hp
    simp only [Finset.mem_product, Set.Finite.mem_toFinset] at hp ⊢
    refine (mem_dbl U _ _).2 fun j => ?_
    by_cases hj : j = i
    · subst hj
      rw [pr_glue_same U j c d (hb' d hp.2), Pi.mul_apply, hb, mul_one]
      exact (mem_dbl U _ _).1 hp.1 j
    · rw [pr_glue_ne U hj, Pi.mul_apply, Pi.mulSingle_eq_of_ne hj, one_mul]
      exact (mem_dbl U _ _).1 hp.2 j
  · rintro ⟨c, d⟩ hp ⟨c', d'⟩ hp' h
    simp only [Finset.mem_product, Set.Finite.mem_toFinset] at hp hp'
    have h' : glue U i c d = glue U i c' d' := h
    refine Prod.ext (pr_ext U fun j => ?_) (pr_ext U fun j => ?_)
    · by_cases hj : j = i
      · subst hj
        rw [← pr_glue_same U j c d (hb' d hp.2), h', pr_glue_same U j c' d' (hb' d' hp'.2)]
      · rw [ha c hp.1 j hj, ha c' hp'.1 j hj]
    · by_cases hj : j = i
      · subst hj
        rw [hb' d hp.2, hb' d' hp'.2]
      · rw [← pr_glue_ne U hj c d, h', pr_glue_ne U hj]
  · intro e he
    rw [Set.Finite.mem_toFinset, mem_dbl] at he
    have hd : pr U i (QuotientGroup.mk (Function.update e.out i 1)) = QuotientGroup.mk 1 := by
      rw [pr_mk, Function.update_self]
    refine ⟨(QuotientGroup.mk (Pi.mulSingle i (e.out i)), QuotientGroup.mk (Function.update e.out i 1)), ?_, ?_⟩
    · simp only [Finset.mem_product, Set.Finite.mem_toFinset, mem_dbl]
      refine ⟨fun j => ?_, fun j => ?_⟩
      · have := he j
        by_cases hj : j = i
        · subst hj
          rw [Pi.mul_apply, hb, mul_one] at this
          rw [pr_mk, Pi.mulSingle_eq_same j (Quotient.out e j)]
          exact this
        · rw [pr_mk, Pi.mulSingle_eq_of_ne hj, Pi.mulSingle_eq_of_ne hj, mem_dbl_one]
      · have := he j
        by_cases hj : j = i
        · subst hj
          rw [hd, hb, mem_dbl_one]
        · rw [Pi.mul_apply, Pi.mulSingle_eq_of_ne hj, one_mul] at this
          rw [pr_mk, Function.update_of_ne hj]
          exact this
    · refine pr_ext U fun j => ?_
      by_cases hj : j = i
      · subst hj
        rw [pr_glue_same U j _ _ hd, pr_mk, Pi.mulSingle_eq_same]
        rfl
      · rw [pr_glue_ne U hj, pr_mk, Function.update_of_ne hj]
        rfl

private theorem hop_one {H V : Type} [Group H] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V)
    {U : Subgroup H} {v : V} (hv : ∀ u ∈ U, ρ u v = v) : hopR ρ U 1 v = v := by
  have h : dbl U 1 = {QuotientGroup.mk 1} := Set.ext fun c => mem_dbl_one U c
  change ∑ᶠ c ∈ dbl U 1, ρ c.out v = v
  rw [h, finsum_mem_singleton, act_congr ρ hv (QuotientGroup.out_eq' _), map_one, Module.End.one_apply]

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.HopfProductGluing

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.HopfProductGluing in
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.hopProd :
    ∀ {r : ℕ} {G : Fin r → Type} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)] {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (∀ i, G i) V) (U : ∀ i, Subgroup (G i)) (Q : Submodule ℂ V), (∀ i, CO (U i)) →
      (∀ v ∈ Q, ∀ u ∈ Subgroup.pi Set.univ U, ρ u v = v) → (∀ i g, ∀ v ∈ Q, hopR ρ (Subgroup.pi Set.univ U) (Pi.mulSingle i g) v ∈ Q) →
      ∀ g, ∀ v ∈ Q, hopR ρ (Subgroup.pi Set.univ U) g v ∈ Q := by
  intro r G _ _ _ V _ _ ρ U Q hU hfix hone
  have key : ∀ s : Finset (Fin r), ∀ g : ∀ i, G i, (∀ j, j ∉ s → g j = 1) →
      ∀ v ∈ Q, hopR ρ (Subgroup.pi Set.univ U) g v ∈ Q := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro g hg v hv
      have : g = 1 := funext fun j => hg j (Finset.notMem_empty j)
      rw [this, hop_one ρ (hfix v hv)]
      exact hv
    | insert i s hi ih =>
      intro g hg v hv
      have hb : hopR ρ (Subgroup.pi Set.univ U) (Function.update g i 1) v ∈ Q := by
        refine ih _ (fun j hj => ?_) v hv
        by_cases hji : j = i
        · subst hji; exact Function.update_self ..
        · rw [Function.update_of_ne hji]
          exact hg j (by simp [hji, hj])
      have e : g = Pi.mulSingle i (g i) * Function.update g i 1 := by
        funext j
        by_cases hji : j = i
        · subst hji; simp
        · simp [Pi.mulSingle_eq_of_ne hji, Function.update_of_ne hji]
      rw [e, hop_mul ρ U hU i (g i) _ (Function.update_self ..) v (hfix v hv) (hfix _ hb)]
      exact hone i _ _ hb
  exact fun g => key Finset.univ g (fun j hj => absurd (Finset.mem_univ j) hj)
end

section

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

private theorem finite_image {G Y : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup Y] [Module ℂ Y]
    (f : G → Y) (hf : f ∈ GlobalTheory.PRep.smoothPart (rightReg ℂ G Y)) (K : Set G) (hK : IsCompact K) : (f '' K).Finite := by
  have hlc : IsLocallyConstant f := by
    refine (IsLocallyConstant.iff_eventually_eq f).2 fun x => ?_
    have ho : IsOpen {g : G | rightReg ℂ G Y g f = f} := hf
    have hc : Continuous fun y : G => x⁻¹ * y := by fun_prop
    have : (fun y : G => x⁻¹ * y) ⁻¹' {g : G | rightReg ℂ G Y g f = f} ∈ nhds x :=
      (ho.preimage hc).mem_nhds (by simp)
    filter_upwards [this] with y hy
    have h2 : f (x * (x⁻¹ * y)) = f x := congrFun hy x
    simpa using h2
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have := (hlc.comp_continuous (continuous_subtype_val (p := (· ∈ K)))).range_finite
  rwa [Set.range_comp, Subtype.range_coe_subtype] at this

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.indTens :
    ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {Γ : Type} [Group Γ] {V : Type} [AddCommGroup V] [Module ℂ V] {B : Type} [AddCommGroup B] [Module ℂ B] (P K : Subgroup G) (ρ : Representation ℂ P V) (m : Representation ℂ Γ B), CO K →
      (∀ g : G, ∃ p ∈ P, ∃ k ∈ K, g = p * k) →
      ∃ e : smoothPart (ind P ρ) ⊗[ℂ] B ≃ₗ[ℂ] IndF P.subtype ((extTensor ρ m).comp (MonoidHom.inl P Γ)) ⊤,
        ∀ a b g, (e (a ⊗ₜ b)).1 g = a.1.1 g ⊗ₜ b := by
  intro G _ _ _ Γ _ V _ _ B _ _ P K ρ m hK hPK
  have hact : ∀ (p : P) (v : V) (b : B),
      ((extTensor ρ m).comp (MonoidHom.inl P Γ)) p (v ⊗ₜ[ℂ] b) = ρ p v ⊗ₜ[ℂ] b := by
    intro p v b
    simp [extTensor]
  let Φ₀ : GlobalTheory.PRep.smoothPart (ind P ρ) →ₗ[ℂ] B →ₗ[ℂ]
      IndF P.subtype ((extTensor ρ m).comp (MonoidHom.inl P Γ)) ⊤ :=
    LinearMap.mk₂ ℂ (fun a b => ⟨fun g => a.1.1 g ⊗ₜ[ℂ] b, ⟨fun _ => trivial, fun h g => by
        rw [hact, ← a.1.2 h g]; rfl⟩, by
        refine GlobalTheory.SmGL.mem_smoothPart_of_nhds (Filter.mem_of_superset (IsOpen.mem_nhds a.2 (by simp)) fun u hu => ?_)
        funext x
        have h2 : a.1.1 (x * u) = a.1.1 x := congrFun (congrArg Subtype.val hu) x
        show a.1.1 (x * u) ⊗ₜ[ℂ] b = a.1.1 x ⊗ₜ[ℂ] b
        rw [h2]⟩)
      (fun a a' b => Subtype.ext (funext fun g => TensorProduct.add_tmul _ _ _))
      (fun c a b => Subtype.ext (funext fun g => (TensorProduct.smul_tmul' _ _ _).symm))
      (fun a b b' => Subtype.ext (funext fun g => TensorProduct.tmul_add _ _ _))
      (fun c a b => Subtype.ext (funext fun g => TensorProduct.tmul_smul _ _ _))
  let Φ := TensorProduct.lift Φ₀
  have hΦ : ∀ a b g, (Φ (a ⊗ₜ b)).1 g = a.1.1 g ⊗ₜ[ℂ] b := fun a b g => rfl
  let β := Module.Basis.ofVectorSpace ℂ B
  let ES := TensorProduct.equivFinsuppOfBasisRight (M := GlobalTheory.PRep.smoothPart (ind P ρ)) β
  let EV := TensorProduct.equivFinsuppOfBasisRight (M := V) β
  have key : ∀ x i g, (ES x i).1.1 g = EV ((Φ x).1 g) i := by
    intro x i g
    induction x using TensorProduct.induction_on with
    | zero =>
      rw [ES.map_zero, Φ.map_zero]
      change (0 : V) = EV 0 i
      rw [EV.map_zero]
      rfl
    | tmul a b =>
      rw [hΦ]
      simp only [ES, EV, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
      rfl
    | add x y hx hy => simp [hx, hy]
  have hEV : ∀ (p : P) y i, EV (((extTensor ρ m).comp (MonoidHom.inl P Γ)) p y) i = ρ p (EV y i) := by
    intro p y i
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rw [hact]
      simp only [EV, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply, map_smul]
    | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]
  refine ⟨LinearEquiv.ofBijective Φ ⟨?_, ?_⟩, hΦ⟩
  · refine (injective_iff_map_eq_zero Φ).2 fun x hx => ?_
    apply ES.injective
    ext i g
    rw [key, hx]
    change EV 0 i = 0
    rw [EV.map_zero]
    rfl
  · intro f
    have hlaw : ∀ (p : P) g, f.1 (p * g) = ((extTensor ρ m).comp (MonoidHom.inl P Γ)) p (f.1 g) := f.2.1.2
    let c : _ → GlobalTheory.PRep.smoothPart (ind P ρ) := fun i =>
      ⟨⟨fun g => EV (f.1 g) i, fun h g => by
          show EV (f.1 (h * g)) i = _
          rw [hlaw, hEV]⟩, by
        refine GlobalTheory.SmGL.mem_smoothPart_of_nhds (Filter.mem_of_superset (IsOpen.mem_nhds f.2.2 (by simp)) fun u hu => ?_)
        apply Subtype.ext
        funext x
        have h2 : f.1 (x * u) = f.1 x := congrFun hu x
        show EV (f.1 (x * u)) i = EV (f.1 x) i
        rw [h2]⟩
    have hfin : (Function.support c).Finite := by
      refine ((finite_image f.1 f.2.2 K hK.1).biUnion (t := fun y => ((EV y).support : Set _))
        fun y _ => Finset.finite_toSet _).subset fun i hi => ?_
      by_contra hn
      apply hi
      apply Subtype.ext
      apply Subtype.ext
      funext g
      obtain ⟨p, hp, k, hk, rfl⟩ := hPK g
      have h0 : EV (f.1 k) i = 0 := by
        by_contra h0
        exact hn (Set.mem_biUnion ⟨k, hk, rfl⟩ (Finsupp.mem_support_iff.2 h0))
      show EV (f.1 (p * k)) i = 0
      rw [hlaw ⟨p, hp⟩ k, hEV, h0, map_zero]
    refine ⟨ES.symm (Finsupp.ofSupportFinite c hfin), Subtype.ext (funext fun g => EV.injective ?_)⟩
    ext i
    rw [← key, LinearEquiv.apply_symm_apply]
    rfl
end

section

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.indSeed :
    ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {H : Type} [Group H] [TopologicalSpace H] {Γ : Type} [Group Γ] {Y : Type} [AddCommGroup Y] [Module ℂ Y] (j : H →* G) (y : Representation ℂ (H × Γ) Y) (v₀ : Y), Topology.IsEmbedding j →
      (∀ N ∈ nhds (1 : G), ∃ U : Subgroup G, IsOpen (U : Set G) ∧ (U : Set G) ⊆ N) → IsOpen {h : H | y (h, 1) v₀ = v₀} →
      ∃ (U : Subgroup G) (F : Y →ₗ[ℂ] (G → Y)), (∀ h, j h ∈ U → y (h, 1) v₀ = v₀) ∧ ∀ v, (∀ h, j h ∈ U → y (h, 1) v = v) →
        F v ∈ IndF j (y.comp (MonoidHom.inl H Γ)) ⊤ ∧ F v 1 = v ∧ ∀ c g, F (y (1, c) v) g = y (1, c) (F v g) := by
  intro G _ _ _ H _ _ Γ _ Y _ _ j y v₀ hj hsm hop
  obtain ⟨N, hN, hNe⟩ := hj.isInducing.isOpen_iff.1 hop
  have h1 : (1 : G) ∈ N := by
    have h0 : (1 : H) ∈ j ⁻¹' N := by
      rw [hNe]
      show y (1, 1) v₀ = v₀
      have : ((1, 1) : H × Γ) = 1 := rfl
      rw [this, map_one]
      rfl
    simpa using h0
  obtain ⟨U, hUo, hUN⟩ := hsm N (hN.mem_nhds h1)
  let D : G → Prop := fun g => ∃ h u, u ∈ U ∧ g = j h * u
  let F : Y →ₗ[ℂ] (G → Y) := LinearMap.pi fun g => if hg : D g then y (hg.choose, 1) else 0
  have Fin' : ∀ g (hg : D g) v, F v g = y (hg.choose, 1) v := by
    intro g hg v
    show (if hg : D g then y (hg.choose, 1) else 0) v = _
    rw [dite_eq_left hg]
  have Fout : ∀ g, ¬ D g → ∀ v, F v g = 0 := by
    intro g hg v
    show (if hg : D g then y (hg.choose, 1) else 0) v = _
    rw [dite_eq_right hg]
    rfl
  refine ⟨U, F, ?_, ?_⟩
  · intro h hh
    have h2 : h ∈ j ⁻¹' N := hUN hh
    rw [hNe] at h2
    exact h2
  · intro v hv
    have key : ∀ g h u, u ∈ U → g = j h * u → F v g = y (h, 1) v := by
      intro g h u hu hg
      have hD : D g := ⟨h, u, hu, hg⟩
      rw [Fin' g hD]
      obtain ⟨u', hu', e⟩ := hD.choose_spec
      generalize hD.choose = c at e
      have hc : j (h⁻¹ * c) ∈ U := by
        have e1 : j h * u = j c * u' := hg.symm.trans e
        have e2 : j (h⁻¹ * c) = u * u'⁻¹ := by
          rw [map_mul, map_inv, inv_mul_eq_iff_eq_mul, ← mul_assoc, e1, mul_inv_cancel_right]
        rw [e2]
        exact U.mul_mem hu (U.inv_mem hu')
      have e3 := hv _ hc
      have e4 : ((c, 1) : H × Γ) = (h, 1) * (h⁻¹ * c, 1) := by simp
      rw [e4, map_mul, Module.End.mul_apply, e3]
    have notD : ∀ a g, ¬ D g → ¬ D (j a * g) := by
      rintro a g hg ⟨b, u, hu, e⟩
      exact hg ⟨a⁻¹ * b, u, hu, by rw [map_mul, map_inv, mul_assoc, ← e, inv_mul_cancel_left]⟩
    have notD' : ∀ g u, u ∈ U → ¬ D g → ¬ D (g * u) := by
      rintro g u hu hg ⟨b, u', hu', e⟩
      exact hg ⟨b, u' * u⁻¹, U.mul_mem hu' (U.inv_mem hu), by rw [← mul_assoc, ← e, mul_inv_cancel_right]⟩
    have hfix : ∀ u ∈ U, rightReg ℂ G Y u (F v) = F v := by
      intro u hu
      funext x
      show F v (x * u) = F v x
      by_cases hx : D x
      · obtain ⟨a, u', hu', rfl⟩ := hx
        rw [key _ a (u' * u) (U.mul_mem hu' hu) (mul_assoc _ _ _), key _ a u' hu' rfl]
      · rw [Fout _ hx, Fout _ (notD' x u hu hx)]
    refine ⟨Submodule.mem_inf.2 ⟨⟨fun _ => Submodule.mem_top, ?_⟩, ?_⟩, ?_, ?_⟩
    · intro h g
      show F v (j h * g) = y (h, 1) (F v g)
      by_cases hg : D g
      · obtain ⟨a, u, hu, rfl⟩ := hg
        rw [key _ (h * a) u hu (by rw [map_mul, mul_assoc]), key _ a u hu rfl]
        have e : ((h * a, 1) : H × Γ) = (h, 1) * (a, 1) := by simp
        rw [e, map_mul, Module.End.mul_apply]
      · rw [Fout _ hg, Fout _ (notD h g hg), map_zero]
    · show IsOpen {x : G | rightReg ℂ G Y x (F v) = F v}
      refine isOpen_iff_mem_nhds.2 fun s hs => ?_
      have hc : Continuous fun x : G => s⁻¹ * x := continuous_const.mul continuous_id
      have hm : {x : G | s⁻¹ * x ∈ U} ∈ nhds s :=
        (hUo.preimage hc).mem_nhds (by simpa using U.one_mem)
      refine Filter.mem_of_superset hm fun x hx => ?_
      have hxs : x = s * (s⁻¹ * x) := by group
      show rightReg ℂ G Y x (F v) = F v
      rw [hxs, map_mul, Module.End.mul_apply, hfix _ hx]
      exact hs
    · rw [key 1 1 1 U.one_mem (by simp)]
      have : ((1, 1) : H × Γ) = 1 := rfl
      rw [this, map_one]
      rfl
    · intro c g
      by_cases hg : D g
      · rw [Fin' g hg, Fin' g hg, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
        congr 2
        simp
      · rw [Fout _ hg, Fout _ hg, map_zero]
end
