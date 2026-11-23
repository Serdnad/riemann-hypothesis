module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FderivFnCongr
public import Mathlib.Algebra.DualNumber
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle857
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle858
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle649
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle505
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle859
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle860
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle861
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle862
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.SpanXLeKerAevalZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_firstOrderJet_algHom : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Opens E) (p : E), p ∈ W → ∀ v : E, ∃ ρ : Hol W →ₐ[ℂ] DualNumber ℂ, ∀ h, (ρ h).fst = h.fn p ∧ (ρ h).snd = fderiv ℂ h.fn p v := by
  first | exact @GlobalTheory.AnPer.Hol.exists_jet_algHom | exact GlobalTheory.AnPer.Hol.exists_jet_algHom | (intros; apply GlobalTheory.AnPer.Hol.exists_jet_algHom <;> assumption)
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

noncomputable section

namespace GlobalTheory.Katz

theorem exists_rigMap (p : ℕ) (k : Type) [Field k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d) :
    ∃ ρ : MvPowerSeries (Fin d ⊕ Fin d) k × (Fin d → k) →ₗ[k] ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n)))))),
      (∀ s w (z : G.cocycles) (u : G.omega), (∀ n, z.1 n = c.ev₂ n s) →
        (∀ n, u.1 n = ∑ i, w i • dUnit (R := k) (c.x n i)) → ρ (s, w) = G.rigMk (z, u)) := by
  classical
  let L : MvPowerSeries (Fin d ⊕ Fin d) k →ₗ[k] (∀ n, G.A n ⊗[k] G.A n) :=
    LinearMap.pi fun n => (c.ev₂ n).toLinearMap
  let S : Submodule k (MvPowerSeries (Fin d ⊕ Fin d) k) := G.cocycles.comap L
  let T₀ : S →ₗ[k] G.cocycles := L.restrict (fun x hx => hx)
  obtain ⟨T, hT⟩ := LinearMap.exists_extend T₀
  have hU := (GlobalTheory.T.invariantDifferentials_connectedPDivGroup_coordinates p k d G c).1
  let U : (Fin d → k) →ₗ[k] G.omega :=
    { toFun := fun w => ⟨fun n => ∑ i, w i • dUnit (R := k) (c.x n i), hU w⟩
      map_add' := fun a b => Subtype.ext (funext fun n => by
        simp [add_smul, Finset.sum_add_distrib])
      map_smul' := fun r a => Subtype.ext (funext fun n => by
        simp [Finset.smul_sum, smul_smul]) }
  refine ⟨G.rigMk ∘ₗ T.prodMap U, fun s w z u hz hu => ?_⟩
  have hs : s ∈ S := by
    change L s ∈ G.cocycles
    have : L s = z.1 := funext fun n => (hz n).symm
    rw [this]; exact z.2
  have h1 : T s = z := by
    have := LinearMap.congr_fun hT ⟨s, hs⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
    rw [this]
    exact Subtype.ext (funext fun n => (hz n).symm)
  have h2 : U w = u := Subtype.ext (funext fun n => (hu n).symm)
  change G.rigMk (T s, U w) = G.rigMk (z, u)
  exact congrArg G.rigMk (Prod.ext h1 h2)

end GlobalTheory.Katz
end
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Katz.CobCoord

variable {p : ℕ} {k : Type} [CommRing k] {d : ℕ} {G : PDivGroup p k}

theorem connectedPDivGroupChart_eval_nilpotent_pair (c : Chart G d) (n : ℕ) {B : Type} [CommRing B] [Algebra k B] {τ : Type} [Finite τ]
    (E : MvPowerSeries τ k →ₐ[k] B) (hE : ∀ t, IsNilpotent (E (X t)))
    (u v : Fin d → MvPowerSeries τ k) (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) (g : G.A n ⊗[k] G.A n →ₐ[k] B)
    (hgu : ∀ i, E (u i) = g (c.x n i ⊗ₜ 1)) (hgv : ∀ i, E (v i) = g (1 ⊗ₜ c.x n i))
    (s : MvPowerSeries (Fin d ⊕ Fin d) k) : E (at2 s u v) = g (c.ev₂ n s) := by
  have hy : ∀ j, IsNilpotent (g (c.x₂ n j)) := fun j => (c.nil₂ n j).map g
  have h1 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d ⊕ Fin d) B).1 τ E hE (Sum.elim u v)
    (by rintro (i | i) <;> simp [hu, hv]) (fun j => g (c.x₂ n j)) hy
    (by rintro (i | i) <;> simp [Chart.x₂, hgu, hgv]) s
  have h2 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d ⊕ Fin d) (G.A n ⊗[k] G.A n)).2 B g (c.x₂ n) (c.nil₂ n)
    (fun j => g (c.x₂ n j)) hy (fun _ => rfl) s
  unfold at2
  rw [h1, Chart.ev₂, h2]

end GlobalTheory.Katz.CobCoord

namespace GlobalTheory.Katz.CobCoord

variable (k : Type) [CommRing k] (A : Type) [CommRing A] [Bialgebra k A]

abbrev gSumL : A ⊗[k] A →ₐ[k] A ⊗[k] (A ⊗[k] A) :=
  (Algebra.TensorProduct.assoc k k k A A A).toAlgHom.comp
    (Algebra.TensorProduct.map (Bialgebra.comulAlgHom k A) (AlgHom.id k A))

abbrev gSumR : A ⊗[k] A →ₐ[k] A ⊗[k] (A ⊗[k] A) :=
  Algebra.TensorProduct.map (AlgHom.id k A) (Bialgebra.comulAlgHom k A)

abbrev gFst : A ⊗[k] A →ₐ[k] A ⊗[k] (A ⊗[k] A) :=
  Algebra.TensorProduct.map (AlgHom.id k A) (Algebra.TensorProduct.includeLeft (S := k))

theorem algAssoc_apply (w : (A ⊗[k] A) ⊗[k] A) :
    Algebra.TensorProduct.assoc k k k A A A w = TensorProduct.assoc k A A A w := by
  induction w with
  | tmul x b =>
    induction x with
    | tmul a a' => simp
    | add x y hx hy => simp only [add_tmul, map_add (f := _), hx, hy]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem gSumL_apply (t : A ⊗[k] A) :
    gSumL k A t = TensorProduct.assoc k A A A (Coalgebra.comul.rTensor A t) := by
  induction t with
  | tmul a b => simp [algAssoc_apply]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem gSumR_apply (t : A ⊗[k] A) : gSumR k A t = Coalgebra.comul.lTensor A t := by
  induction t with
  | tmul a b => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem gFst_apply (t : A ⊗[k] A) :
    gFst k A t = ((TensorProduct.mk k A A).flip 1).lTensor A t := by
  induction t with
  | tmul a b => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem gFst_eq_assoc (t : A ⊗[k] A) :
    gFst k A t = Algebra.TensorProduct.assoc k k k A A A (t ⊗ₜ 1) := by
  induction t with
  | tmul a b => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy, add_tmul]

theorem cobTwo_eq (t : A ⊗[k] A) : cobTwo k A t =
    Algebra.TensorProduct.includeRight t - gSumL k A t + gSumR k A t - gFst k A t := by
  rw [cobTwo_apply, gSumL_apply, gSumR_apply, gFst_apply, Algebra.TensorProduct.includeRight_apply]

end GlobalTheory.Katz.CobCoord

namespace GlobalTheory.Katz.CobCoord

theorem evA_cob2_eq_cobTwo_and_op_assoc : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d),
    ∀ (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), c.IsLawOf μ →
    ∀ n (h : ∀ i, IsNilpotent ((Sum.elim (fun i => c.x n i ⊗ₜ[k] (1 : G.A n ⊗[k] G.A n))
      (fun j => (1 : G.A n) ⊗ₜ[k] c.x₂ n j)) i)),
    (∀ s, evA k _ h (cob2 μ s) = cobTwo k (G.A n) (c.ev₂ n s)) ∧
      ∀ i, evA k _ h (op μ (op μ x1 x2) x3 i) = evA k _ h (op μ x1 (op μ x2 x3) i) := by
  intro p k _ d G c μ hμ n h
  have hX := GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate k _ _ _ h
  have hE : ∀ t, IsNilpotent (evA k _ h (X t)) := fun t => by rw [hX]; exact h t
  have hμ0 := ((GlobalTheory.T.connectedPDivGroup_formalLaw_coordinates p k d G c).2 μ hμ).1
  have e1 : ∀ i, evA k _ h (x1 i) = c.x n i ⊗ₜ 1 := fun i => hX (Sum.inl i)
  have e2 : ∀ i, evA k _ h (x2 i) = 1 ⊗ₜ (c.x n i ⊗ₜ 1) := fun i => hX (Sum.inr (Sum.inl i))
  have e3 : ∀ i, evA k _ h (x3 i) = 1 ⊗ₜ (1 ⊗ₜ c.x n i) := fun i => hX (Sum.inr (Sum.inr i))
  have c1 : ∀ i, constantCoeff (x1 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k) = 0 :=
    fun _ => constantCoeff_X _
  have c2 : ∀ i, constantCoeff (x2 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k) = 0 :=
    fun _ => constantCoeff_X _
  have c3 : ∀ i, constantCoeff (x3 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k) = 0 :=
    fun _ => constantCoeff_X _
  have cop : ∀ u v : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k,
      (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) →
      ∀ i, constantCoeff (op μ u v i) = 0 := by
    intro u v hu hv i
    have hs : ∀ j, constantCoeff (Sum.elim u v j) = 0 := by rintro (j | j) <;> simp [hu, hv]
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hs) hs (hμ0 i)
  have o12 : ∀ i, evA k _ h (op μ x1 x2 i) = gFst k (G.A n) (Coalgebra.comul (c.x n i)) := by
    intro i
    rw [op, connectedPDivGroupChart_eval_nilpotent_pair c n _ hE x1 x2 c1 c2 (gFst k (G.A n)) (fun j => by rw [e1]; simp [Algebra.TensorProduct.one_def])
      (fun j => by rw [e2]; simp [Algebra.TensorProduct.one_def]), hμ n i]
  have o23 : ∀ i, evA k _ h (op μ x2 x3 i) =
      Algebra.TensorProduct.includeRight (Coalgebra.comul (c.x n i)) := by
    intro i
    rw [op, connectedPDivGroupChart_eval_nilpotent_pair c n _ hE x2 x3 c2 c3 Algebra.TensorProduct.includeRight
      (fun j => by rw [e2]; simp [Algebra.TensorProduct.one_def]) (fun j => by rw [e3]; simp [Algebra.TensorProduct.one_def]), hμ n i]
  have a2 := connectedPDivGroupChart_eval_nilpotent_pair c n _ hE (op μ x1 x2) x3 (cop _ _ c1 c2) c3 (gSumL k (G.A n))
    (fun j => by rw [o12, gFst_eq_assoc]; simp)
    (fun j => by rw [e3]; simp [Algebra.TensorProduct.one_def])
  have a3 := connectedPDivGroupChart_eval_nilpotent_pair c n _ hE x1 (op μ x2 x3) c1 (cop _ _ c2 c3) (gSumR k (G.A n))
    (fun j => by rw [e1]; simp [Algebra.TensorProduct.one_def]) (fun j => by rw [o23]; simp)
  refine ⟨fun s => ?_, fun i => ?_⟩
  · have a1 := connectedPDivGroupChart_eval_nilpotent_pair c n _ hE x2 x3 c2 c3 Algebra.TensorProduct.includeRight
      (fun j => by rw [e2]; simp [Algebra.TensorProduct.one_def]) (fun j => by rw [e3]; simp [Algebra.TensorProduct.one_def]) s
    have a4 := connectedPDivGroupChart_eval_nilpotent_pair c n _ hE x1 x2 c1 c2 (gFst k (G.A n))
      (fun j => by rw [e1]; simp [Algebra.TensorProduct.one_def]) (fun j => by rw [e2]; simp [Algebra.TensorProduct.one_def]) s
    rw [cob2, map_sub, map_add (f := _), map_sub, a1, a2, a3, a4, cobTwo_eq]
  · change evA k _ h (at2 (μ i) (op μ x1 x2) x3) = evA k _ h (at2 (μ i) x1 (op μ x2 x3))
    rw [a2, a3, hμ n i, gSumL_apply, gSumR_apply, Coalgebra.coassoc_apply]

end GlobalTheory.Katz.CobCoord
end
end

section

open GlobalTheory.ExpFrame

theorem _root_.GlobalTheory.T.frameCoeffRing_prime_not_isUnit : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) (N : ℕ) (F : Frame l ι N), F.Ok → ¬ IsUnit ((l : ℕ) : F.O) := by
  first | exact @GlobalTheory.ExpFrame.Frame.prime_not_isUnit | exact GlobalTheory.ExpFrame.Frame.prime_not_isUnit | (intros; apply GlobalTheory.ExpFrame.Frame.prime_not_isUnit <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

theorem _root_.GlobalTheory.T.hasBlocks_of_system_occurs_in_block_part : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (G0 : Type) [Group G0] [Fintype G0] (Pl0 : Type) (B : BlockDat K G0 Pl0) (w : HeightOneSpectrum (𝓞 K)) (l : ℕ) [Fact l.Prime] (ι : Type) [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (lam : ι → ℕ → ℕ) (R : Reads F lam B w) (Z : Submodule K B.S.Forms), (∀ P, B.op (P, 0) = 1) → Z ≤ B.ZH → ∀ θ, R.Occurs Z θ → R.HasBlock θ ∧ F.IsEig lam θ := by
  first | exact @GlobalTheory.OccBlock.hasBlock_of_occurs | exact GlobalTheory.OccBlock.hasBlock_of_occurs | (intros; apply GlobalTheory.OccBlock.hasBlock_of_occurs <;> assumption)
end

section

open GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative

theorem _root_.GlobalTheory.T.isUnit_natCast_frameCoeffRing_not_dvd : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [DecidableEq ι] (N : ℕ) (F : Frame l ι N), F.Ok → ∀ n : ℕ, ¬ l ∣ n → IsUnit (n : F.O) := by
  first | exact @GlobalTheory.ExpFrame.Frame.isUnit_natCast_of_not_dvd | exact GlobalTheory.ExpFrame.Frame.isUnit_natCast_of_not_dvd | (intros; apply GlobalTheory.ExpFrame.Frame.isUnit_natCast_of_not_dvd <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

theorem _root_.GlobalTheory.T.existsUnique_dualWeylWeightProjector : ∀ (O : Type) [CommRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ) (τ : ι) (w : Fin N → ℕ), ∃ a, IsProj O N lam τ w a ∧ ∀ a', IsProj O N lam τ w a' → a' = a := by
  first | exact @GlobalTheory.ExpFrame.exists_unique_isProj | exact GlobalTheory.ExpFrame.exists_unique_isProj | (intros; apply GlobalTheory.ExpFrame.exists_unique_isProj <;> assumption)
end

section

open GlobalTheory.ExpFrame

theorem _root_.GlobalTheory.T.finite_frameCoeffRing_quotient_prime : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) (N : ℕ) (F : Frame l ι N), F.Ok → Finite (F.O ⧸ Ideal.span {((l : ℕ) : F.O)}) := by
  first | exact @GlobalTheory.FrameQuot.finite_quot_prime | exact GlobalTheory.FrameQuot.finite_quot_prime | (intros; apply GlobalTheory.FrameQuot.finite_quot_prime <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

theorem _root_.GlobalTheory.T.heckeStable_of_heckeFrame_polynomial_action : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (lam : ι → ℕ → ℕ) (jK : F.K →* alg F.O N lam) [Module F.T (Forms F.O (A := alg F.O N lam) F.Γ jK (NablaT F.O N lam))] (W : Type) [AddCommGroup W] [Module F.O W] [Module (alg F.O N lam) W] [IsScalarTower F.O (alg F.O N lam) W] [Module F.T (Forms F.O (A := alg F.O N lam) F.Γ jK W)], F.IsHecke lam jK (NablaT F.O N lam) → F.IsHecke lam jK W → HeckeStable F.O (A := alg F.O N lam) F.Γ jK F.T (NablaT F.O N lam) ∧ HeckeNat F.O (A := alg F.O N lam) F.Γ jK F.T (NablaT F.O N lam) W := by
  first | exact @GlobalTheory.ExpFrame.heckeStable_heckeNat_of_isHecke | exact GlobalTheory.ExpFrame.heckeStable_heckeNat_of_isHecke | (intros; apply GlobalTheory.ExpFrame.heckeStable_heckeNat_of_isHecke <;> assumption)
end

section

open GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative

theorem _root_.GlobalTheory.T.linearIndependent_frameForms_baseChange : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (mu : ι → ℕ → ℕ) (jK : F.K →* alg F.O N mu) (b : NablaT F.O N mu →ₛₗ[F.emb] NablaT (PadicAlgCl l) N mu), Function.Injective b → F.Ok → (∀ (n : ℕ) (x : Fin n → NablaT F.O N mu), LinearIndependent F.O x → LinearIndependent (PadicAlgCl l) fun a => b (x a)) → ∀ (n : ℕ) (x : Fin n → Forms F.O (A := alg F.O N mu) F.Γ jK (NablaT F.O N mu)), LinearIndependent F.O x → LinearIndependent (PadicAlgCl l) fun a => (fun g => b ((x a : F.G → NablaT F.O N mu) g)) := by
  first | exact @GlobalTheory.BaseChangeIndep.forms_indep | exact GlobalTheory.BaseChangeIndep.forms_indep | (intros; apply GlobalTheory.BaseChangeIndep.forms_indep <;> assumption)
end

section

open GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative

theorem _root_.GlobalTheory.T.module_finite_frameLatticeForms : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (mu : ι → ℕ → ℕ) (jK : F.K →* alg F.O N mu), F.Ok → Module.Finite F.O (Forms F.O (A := alg F.O N mu) F.Γ jK (NablaT F.O N mu)) := by
  first | exact @GlobalTheory.ExpFrame.Frame.finite_latticeForms | exact GlobalTheory.ExpFrame.Frame.finite_latticeForms | (intros; apply GlobalTheory.ExpFrame.Frame.finite_latticeForms <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

theorem _root_.GlobalTheory.T.blockData_of_congruent_heckeSystem : GlobalTheory.Published.ChebotarevDegreeOne → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Type) [DecidableEq ι] (inc : ι → (E →+* PadicAlgCl l)) (P : Par) (W : Wts ι) (F : Frame l ι P.Nr) (Bk : (F.I → PadicAlgCl l) → Prop), GalSide Ω inc P W F Bk → ∀ (mu : ι → ℕ → ℕ) (θ θ0 : F.I → PadicAlgCl l), (∀ τ, Antitone (res P.Nr (mu τ))) → F.IsEig mu θ → F.IsEig W.lam θ0 → Bk θ0 → (∀ i, ‖θ i - θ0 i‖ < 1) → BlockFor Ω inc P W mu := by
  first | exact @GlobalTheory.ExpFrame.CongrBlock.blockFor_of_congr | exact GlobalTheory.ExpFrame.CongrBlock.blockFor_of_congr | (intros; apply GlobalTheory.ExpFrame.CongrBlock.blockFor_of_congr <;> assumption)
end
