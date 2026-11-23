module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1568
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1570
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1571
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1367
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1544
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1569
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle043
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.ZeroNotAdmissibleOfRankPos
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1572
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1578
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatProductFormula
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
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
import Mathlib.RingTheory.PiTensorProduct
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.ThetaValues.PolyDerivSmulLetter

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

theorem _root_.GlobalTheory.T.exists_residueMap_closure_point : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (z : X) (k : ℕ),
  topologicalKrullDim (closure ({z} : Set X)) = k →
  ∃ (κ : Type) (_ : Field κ) (_ : Algebra ℂ κ) (π₀ : locRing z →+* κ),
    Function.Surjective π₀ ∧ (∀ r : locRing z, π₀ r = 0 ↔ ZeroAt z (r : X.functionField)) ∧
    (∀ a (h : Cartier.constFn p a ∈ locRing z), π₀ ⟨Cartier.constFn p a, h⟩ = algebraMap ℂ κ a) ∧
    (∃ w : Fin k → κ, TrBasis (algebraMap ℂ κ) w) ∧
    ∀ (x : X) (h : locRing x ≤ locRing z), IsLocModel (algebraMap ℂ κ) (π₀.comp (Subring.inclusion h)).range ∧
      (∀ f : κ, ∃ a b : locRing x, π₀ (Subring.inclusion h b) ≠ 0 ∧ f * π₀ (Subring.inclusion h b) = π₀ (Subring.inclusion h a)) ∧
      (IsClosed ({x} : Set X) → RatRes (algebraMap ℂ κ) (π₀.comp (Subring.inclusion h)).range) := by
  first | exact @GlobalTheory.ResMap.residueMap | exact GlobalTheory.ResMap.residueMap | (intros; apply GlobalTheory.ResMap.residueMap <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

theorem _root_.GlobalTheory.T.coheight_one_iff_pointClosure_dim_projArith : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsAmb q → ∀ e : ℕ, topologicalKrullDim Y = (e + 1 : ℕ) → (∀ z : Y, Order.coheight z = 1 ↔ HasDim z e) ∧ ∀ (z : Y) (w : clo z), Order.coheight z = 1 → (topologicalKrullDim (clo z) = e ∧ (Order.coheight w = 1 ↔ Order.coheight (cloι z w) = 2)) := by
  first | exact @GlobalTheory.MixHt.dimOne | exact GlobalTheory.MixHt.dimOne | (intros; apply GlobalTheory.MixHt.dimOne <;> assumption)
end

section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

theorem _root_.GlobalTheory.T.isLocallyBlockUnitary_of_iSup_intertwiner_range : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), ∀ (M' : Type) [AddCommGroup M'] [Module ℂ M'] (F' : ι → ι → Module.End ℂ M') (G : Set (M →ₗ[ℂ] M')), (∀ f ∈ G, ∀ a b, s a = s b → ∀ x, f (F a b x) = F' a b (f x)) → (⨆ f ∈ G, LinearMap.range f) = ⊤ → LocU s F → LocU s F' := by
  first | exact @GlobalTheory.HoweR.locU_of_iSup_range_eq_top | exact GlobalTheory.HoweR.locU_of_iSup_range_eq_top | (intros; apply GlobalTheory.HoweR.locU_of_iSup_range_eq_top <;> assumption)
end

section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

theorem _root_.GlobalTheory.T.blockDiagonal_eigenvalue_le_of_casimir_nearMin : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (s : ι → Bool) (α β : ℂ), ∃ R : ℝ, ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (F : ι → ι → Module.End ℂ M), IsGl F → (∀ a b, qop F α β a b = 0) → LocU s F → ∀ ω : ℝ, (∀ (ω' : ℝ) (v : M), v ≠ 0 → cas s F v = (ω' : ℂ) • v → ω < ω' + 1) → ∀ (x : ℝ) (y : ι → M), y ≠ 0 → (∀ a, s a = false → y a = 0) → (∀ a, s a = true → ∑ b, F a b (y b) = (x : ℂ) • y a) → (∀ a, cas s F (y a) = (ω : ℂ) • y a) → x ≤ R := by
  first | exact @GlobalTheory.HoweR.diag_eig_le_of_cas_min | exact GlobalTheory.HoweR.diag_eig_le_of_cas_min | (intros; apply GlobalTheory.HoweR.diag_eig_le_of_cas_min <;> assumption)
end

section

noncomputable section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

namespace GlobalTheory.HoweD

theorem sumPl_single_add_smul {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)]
    [∀ i, Module ℂ (V i)] (L : ∀ w, Module.End ℂ (V w)) (a : ι → ℂ) (w : ι) (hL : ∀ v, v ≠ w → L v = 0) :
    sumPl (fun v => L v + a v • (1 : Module.End ℂ (V v))) =
      atPl w (L w) + (∑ v, a v) • (1 : Module.End ℂ (⨂[ℂ] i, V i)) := by
  have h : ∀ w, atPl w (L w + a w • (1 : Module.End ℂ (V w))) = atPl w (L w) + a w • (1 : Module.End ℂ (⨂[ℂ] i, V i)) := by
    intro w
    have e := (PiTensorProduct.mapMultilinear ℂ V V).map_update_add (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w (L w)
      (a w • LinearMap.id)
    have e2 := (PiTensorProduct.mapMultilinear ℂ V V).map_update_smul (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w (a w)
      LinearMap.id
    simp only [PiTensorProduct.mapMultilinear_apply, Function.update_eq_self, PiTensorProduct.map_id] at e e2
    simp only [atPl]
    rw [Module.End.one_eq_id, Module.End.one_eq_id, e, e2]
    rfl
  have h0 : ∀ v, v ≠ w → atPl v (L v) = (0 : Module.End ℂ (⨂[ℂ] i, V i)) := by
    intro v hv
    rw [hL v hv]
    exact (PiTensorProduct.mapMultilinear ℂ V V).map_update_zero (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) v
  simp only [sumPl, h, Finset.sum_add_distrib, Finset.sum_smul]
  rw [Finset.sum_eq_single w (fun v _ hv => h0 v hv) (fun hw => absurd (Finset.mem_univ w) hw)]

theorem stab_comap_of_thetaSubInf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (om : Rep σ X W) (τ : ∀ w : InfinitePlace F, EmbOver E w) (P Q R S : InfinitePlace F → ℕ) (Φ : TensD F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)) (c : InfinitePlace F → ℂ) (N : Submodule ℂ (SInf F (Fin n × Fin d))), IsCMExt F E σ → GlobalTheory.Published.ThetaSubInf M ψ τ om N → ∀ C : ∀ w : InfinitePlace F, Matrix (Fin d) (Ix (R w) (S w)) ℂ, (∀ w, IsFrame (Complex.I • (incM F W.J).map (piInf (τ w))) (C w)) → ActsByD τ C (om.comp (MonoidHom.inr _ _)) Φ (fun w => fockAct2 (P w) (Q w) (R w) (S w)) c → ∀ w, GlobalTheory.HoweR.Stab (GlobalTheory.HoweR.actAt (V := fun w => Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)) w (fockAct2 (P w) (Q w) (R w) (S w))) (N.comap Φ) := by
  intro F E _ _ _ _ _ σ n d X W M ψ om τ P Q R S Φ c N hCM hN C hC hact w
  have key : ∀ Z ∈ upq (R w) (S w), ∀ y ∈ N.comap Φ,
      GlobalTheory.HoweR.actAt (V := fun w => Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)) w (fockAct2 (P w) (Q w) (R w) (S w)) Z y
        ∈ N.comap Φ := by
    intro Z hZ y hy
    set Y : ∀ v : InfinitePlace F, Mat (R v) (S v) := Pi.single w Z with hYdef
    have hYw : Y w = Z := by simp [hYdef]
    have hYv : ∀ v, v ≠ w → Y v = 0 := fun v hv => by simp [hYdef, Pi.single_eq_of_ne hv]
    have hY : ∀ v, Y v ∈ upq (R v) (S v) := by
      intro v
      by_cases hv : v = w
      · subst hv; rw [hYw]; exact hZ
      · rw [hYv v hv]; simp [upq]
    obtain ⟨γ, hγ, hgen⟩ := GlobalTheory.T.exists_oneParameterSubgroup_unitary_of_realPlace_lieAlg F E σ (Fin d) R S τ (incM F W.J) Complex.I C hCM hC Y hY
    have hSD := hact γ hγ Y hgen y
    have hD := (actsLaws F (Fin n × Fin d) _ _ (Φ y)).1 _ (fun t => map_zero _) hSD
    have hmem := hN.2.2.2.1 γ hγ (Φ y) hy _ hD
    rw [sumPl_single_add_smul (fun v => fockAct2 (P v) (Q v) (R v) (S v) (Y v)) (fun v => c v * (Y v).trace) w
      (fun v hv => by simp only [hYv v hv, map_zero]), hYw, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.one_apply, map_add, map_smul] at hmem
    exact (N.add_mem_iff_left (N.smul_mem _ hy)).1 hmem
  intro Z y hy
  obtain ⟨A, hA, B, hB, rfl⟩ := GlobalTheory.T.exists_indefiniteUnitaryLieAlg_add_I_smul_eq _ _ Z
  rw [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply]
  exact add_mem (key A hA y hy) (Submodule.smul_mem _ _ (key B hB y hy))

end GlobalTheory.HoweD

end
end

section

noncomputable section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

namespace GlobalTheory.HoweD

section Tensor

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

theorem coinv_atPl_tprod (w : ι) (L : Module.End ℂ (V w)) (f : ∀ i, V i) :
    atPl w L (PiTensorProduct.tprod ℂ f) = PiTensorProduct.tprod ℂ (Function.update f w (L (f w))) := by
  unfold atPl
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext i
  by_cases h : i = w
  · subst h
    simp
  · simp [Function.update_of_ne h]

theorem coinv_sumPl_tprod (w : ι) (L : ∀ i, Module.End ℂ (V i)) (hL : ∀ i, i ≠ w → L i = 0) (f : ∀ i, V i) :
    sumPl L (PiTensorProduct.tprod ℂ f) = PiTensorProduct.tprod ℂ (Function.update f w (L w (f w))) := by
  unfold sumPl
  rw [LinearMap.sum_apply, Finset.sum_eq_single w, coinv_atPl_tprod]
  · intro i _ hi
    rw [coinv_atPl_tprod, hL i hi, LinearMap.zero_apply, MultilinearMap.map_update_zero]
  · intro h
    exact absurd (Finset.mem_univ w) h

end Tensor

theorem tensAny_coinv_le_comap : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (om : Rep σ X W) (τ : ∀ w : InfinitePlace F, EmbOver E w) (P Q R S : InfinitePlace F → ℕ) (Φ : TensD F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)) (c : InfinitePlace F → ℂ) (N : Submodule ℂ (SInf F (Fin n × Fin d))), IsCMExt F E σ → GlobalTheory.Published.ThetaSubInf M ψ τ om N → LinearMap.range Φ = M.Pol ψ τ → ∀ A : ∀ w : InfinitePlace F, Matrix (Fin n) (Ix (P w) (Q w)) ℂ, (∀ w, IsFrame ((1 : ℂ) • (incM F X.J).map (piInf (τ w))) (A w)) → ActsByD τ A (om.comp (MonoidHom.inl _ _)) Φ (fun w => fockAct1 (P w) (Q w) (R w) (S w)) c → GlobalTheory.HoweR.tensAny (fun w => GlobalTheory.HoweR.coinv (P w) (Q w) (R w) (S w) (-c w)) ≤ N.comap Φ := by
  intro F E _ _ _ _ _ σ n d X W M ψ om τ P Q R S Φ c N hCM hN hr A hA hact
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, ⟨w, hw⟩, rfl⟩
  let e : Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w) →ₗ[ℂ] TensD F P Q R S := (PiTensorProduct.tprod ℂ).toLinearMap f w
  have he : ∀ g, e g = PiTensorProduct.tprod ℂ (Function.update f w g) := fun g => rfl
  have key : ∀ Z ∈ upq (P w) (Q w), ∀ g,
      fockAct1 (P w) (Q w) (R w) (S w) Z g - (-c w * Z.trace) • g ∈ (N.comap Φ).comap e := by
    intro Z hZ g
    let Y : ∀ i : InfinitePlace F, Mat (P i) (Q i) := Pi.single w Z
    have hY : ∀ i, Y i ∈ upq (P i) (Q i) := by
      intro i
      by_cases h : i = w
      · subst h
        simpa [Y] using hZ
      · simp [Y, Pi.single_eq_of_ne h, upq]
    obtain ⟨γ, hγ, hgen⟩ := GlobalTheory.T.exists_oneParameterSubgroup_unitary_of_realPlace_lieAlg F E σ (Fin n) P Q τ (incM F X.J) 1 A hCM hA Y hY
    have h1 := hact γ hγ Y hgen (e g)
    have h2 := (actsLaws F (Fin n × Fin d) _ _ 0).1 _ (fun t => map_zero _) h1
    have h3 := hN.2.1 γ hγ _ (hr ▸ LinearMap.mem_range_self Φ (e g)) _ h2
    rw [he, coinv_sumPl_tprod w _ (fun i hi => by simp [Y, Pi.single_eq_of_ne hi])] at h3
    rw [Submodule.mem_comap, Submodule.mem_comap, he]
    simpa [Y, sub_eq_add_neg] using h3
  have hle : GlobalTheory.HoweR.coinv (P w) (Q w) (R w) (S w) (-c w) ≤ (N.comap Φ).comap e := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨Z, g, rfl⟩
    obtain ⟨Z₁, h₁, Z₂, h₂, rfl⟩ := GlobalTheory.T.exists_indefiniteUnitaryLieAlg_add_I_smul_eq _ _ Z
    have h := Submodule.add_mem _ (key Z₁ h₁ g) (Submodule.smul_mem _ Complex.I (key Z₂ h₂ g))
    rw [SetLike.mem_coe]
    convert h using 1
    simp only [map_add (f := _), map_smul, Matrix.trace_add, Matrix.trace_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    module
  have h := hle hw
  rw [Submodule.mem_comap, he, Function.update_eq_self] at h
  exact h

end GlobalTheory.HoweD

end
end

section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HatInt

noncomputable section

theorem omegaK_congr {D : D7} {a b : ℕ} (Pg : Finset (Formalism.L2.DIV.Pl D.host.E))
    (y y' : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP))
    (h : ∀ PP ∈ Pg, y PP = y' PP) : omegaK Pg y = omegaK Pg y' := by
  unfold omegaK
  refine if_congr (forall₂_congr fun PP hP => ?_) rfl rfl
  rw [h PP hP]

theorem omegaQ_congr {D : D7} {a b : ℕ} (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (r : ℕ)
    (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (k : ℤ)
    (y y' : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP))
    (h : ∀ PP ∈ Q, y PP = y' PP) : omegaQ Q r ξ k y = omegaQ Q r ξ k y' := by
  unfold omegaQ
  refine dite_congr (propext (forall₂_congr fun PP hP => by rw [h PP hP])) (fun h1 => ?_) (fun _ => rfl)
  refine Finset.prod_congr rfl fun PP _ => ?_
  congr 3
  apply Units.ext
  simp only [IsUnit.unit_spec]
  rw [h PP.1 PP.2]

theorem matrix_map_ringHom_add_smul_sandwich {K S : Type} [CommRing K] [CommRing S] (f : K →+* S) {m n : Type} [Fintype m] [Fintype n]
    (B : Matrix m m S) (C : Matrix n n S) (P : Matrix m m K) (Q : Matrix n n K) (X Y : Matrix m n K) (d : K) :
    B * (P * (X + d • Y) * Q).map f * C = B * (P * X * Q).map f * C + f d • (B * (P * Y * Q).map f * C) := by
  have h2 : ∀ (P Q : Matrix m n K), (P + d • Q).map f = P.map f + f d • Q.map f := by
    intro P Q; ext b a; simp
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, h2]

theorem uMat_add_smul {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D)
    (X Y : Fin S.rank → Fin T.rank → D.host.E) (c : D.host.E) :
    FWT.uMat S T βS βT e (fun b => X b + c • Y b) =
      fun b a => FWT.uMat S T βS βT e X b a + eToEAf D (D.sp.cm.sig c) * FWT.uMat S T βS βT e Y b a := by
  have h1 : (Matrix.of fun b a => D.sp.cm.sig ((X b + c • Y b) a)) =
      (Matrix.of fun b a => D.sp.cm.sig (X b a)) + D.sp.cm.sig c • (Matrix.of fun b a => D.sp.cm.sig (Y b a)) := by
    ext b a; simp
  funext b a
  have h2 := congrFun (congrFun (matrix_map_ringHom_add_smul_sandwich (eToEAf D) (βS⁻¹).val βT.val S.gram⁻¹ T.gram
    (Matrix.of fun b a => D.sp.cm.sig (X b a)) (Matrix.of fun b a => D.sp.cm.sig (Y b a)) (D.sp.cm.sig c)) b) a
  rw [← h1, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at h2
  have h3 := congrArg (fun u => toEAf D e * u) h2
  simp only [mul_add] at h3
  rw [mul_left_comm] at h3
  exact h3

theorem subring_reduction_add_mul_killed {S k : Type} [CommRing S] [CommRing k] (O : Subring S) (f : O →+* k) (x y : S) (hx : x ∈ O) (hy : y ∈ O)
    (c : O) (hc : f c = 0) :
    (if h : x + (c : S) * y ∈ O then f ⟨x + (c : S) * y, h⟩ else 0) = if h : x ∈ O then f ⟨x, h⟩ else 0 := by
  have hmem : x + (c : S) * y ∈ O := add_mem hx (mul_mem c.2 hy)
  rw [dite_eq_left hmem, dite_eq_left hx]
  have : (⟨_, hmem⟩ : O) = ⟨x, hx⟩ + c * ⟨y, hy⟩ := rfl
  rw [this, map_add (f := _), map_mul, hc, zero_mul, add_zero]

theorem redM_add_smul {D : D7} (PP : Formalism.L2.DIV.Pl D.host.E) {b a : ℕ} (N N' : Matrix (Fin b) (Fin a) (EAf D))
    (hN : Datum.IsIntM N) (hN' : Datum.IsIntM N') (s : 𝓞 D.host.E) (hs : s ∈ PP.asIdeal) :
    Datum.redM PP (fun i j => N i j + eToEAf D (s : D.host.E) * N' i j) = Datum.redM PP N := by
  funext i j
  have h0 : ((Formalism.L2.DIV.oToS D.host.F D.host.E s : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) =
      eToEAf D (s : D.host.E) := by
    unfold Formalism.L2.DIV.oToS eToEAf
    rw [RingHom.codRestrict_apply]
    rfl
  rw [← h0]
  unfold Datum.redM
  exact subring_reduction_add_mul_killed _ (Formalism.L2.DIV.resS D.host.F PP) _ _ (hN i j) (hN' i j) _
    (by rw [Formalism.L2.DIV.resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 hs])

theorem sig_bar {D : D7} (H : Geo.Tor.Host D.host.E) (s : 𝓞 D.host.E) :
    D.sp.cm.sig ((H.bar s : 𝓞 D.host.E) : D.host.E) = (s : D.host.E) := by
  rw [H.bar_eq]
  exact IsCMField.complexConj_apply_apply D.host.E (s : D.host.E)

theorem dvd_of_invariant {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H}
    (l : Geo.Tor.Level H) {n : ℕ} (φ : (Fin n → LevQc Dw l) → ℂ) (q : Fin n → LevQ Dw l) (hq : hatC l φ q ≠ 0)
    (z : Fin n → Dw.La) (hφ : ∀ x, φ (x + fun b => Submodule.Quotient.mk (z b)) = φ x) :
    (l.M : ℤ) ∣ Formalism.L2.Pj.pairL (l := l) z (fun b => levRep (q b)) := by
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  have hp := Complex.isPrimitiveRoot_exp l.M hM
  set ζ := Complex.exp (2 * Real.pi * Complex.I / (l.M : ℂ)) with hζ
  have h0 : ζ ≠ 0 := hp.ne_zero hM
  have hrep : ∀ y : LevQc Dw l, Submodule.Quotient.mk (qRep y) = y := fun y =>
    Classical.choose_spec (Submodule.Quotient.mk_surjective _ y)
  have key : hatC l φ q = ζ ^ Formalism.L2.Pj.pairL (l := l) z (fun b => levRep (q b)) * hatC l φ q := by
    unfold hatC
    rw [mul_finsum, ← finsum_comp_equiv (Equiv.addRight (fun b => (Submodule.Quotient.mk (z b) : LevQc Dw l)))]
    refine finsum_congr fun x => ?_
    simp only [Equiv.coe_addRight]
    rw [hφ, mul_left_comm, ← zpow_add₀ h0]
    congr 1
    have hd := LevelPairing.pairL_congr (l := l)
      (fun b => qRep ((x + fun b => (Submodule.Quotient.mk (z b) : LevQc Dw l)) b)) (fun b => z b + qRep (x b))
      (fun b => levRep (q b)) (fun b => levRep (q b))
      (fun b => (Submodule.Quotient.eq _).1 (by
        rw [hrep, Submodule.Quotient.mk_add, hrep, add_comm]; rfl)) (fun b => by simp)
    have ha : Formalism.L2.Pj.pairL (l := l) (fun b => z b + qRep (x b)) (fun b => levRep (q b)) =
        Formalism.L2.Pj.pairL (l := l) z (fun b => levRep (q b)) +
          Formalism.L2.Pj.pairL (l := l) (fun b => qRep (x b)) (fun b => levRep (q b)) := by
      simp [Formalism.L2.Pj.pairL, Finset.sum_add_distrib]
    rw [← ha]
    have := (hp.zpow_eq_one_iff_dvd _).2 hd
    rwa [zpow_sub₀ h0, div_eq_one_iff_eq (zpow_ne_zero _ h0)] at this
  rw [← hp.zpow_eq_one_iff_dvd]
  exact (mul_left_eq_self₀.1 key.symm).resolve_right hq

theorem smul_eq_of_hatC_ne_zero : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)) (t : T0) (l₂ : Geo.Tor.Level H) (φ : (Fin (Vc D i).rank → LevQc Dw l₂) → ℂ), PhiIs R i (RingHom.id ℂ) t ι (Mfr l₂ • ⊤) φ → ∀ q : Fin (Vc D i).rank → LevQ Dw l₂, hatC l₂ φ q ≠ 0 → ∀ s : 𝓞 D.host.E, (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → s ∈ PP.asIdeal) → ∀ b, ∃ z : Dw.La, s • (cSep l₂ • levRep (q b)) = l₂.M • z := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R i H Dw ι t l₂ φ hφ q hq s hs b
  obtain ⟨e, -, he⟩ := hφ
  have hM : l₂.M ≠ 0 := by have := l₂.three_le; omega
  have hdvd : ∀ w : Dw.La, (l₂.M : ℤ) ∣ Dw.EF w (s • (cSep l₂ • levRep (q b))) := by
    intro w
    have h1 := dvd_of_invariant l₂ φ q hq (fun b' => H.bar s • (Pi.single b w : Fin (Vc D i).rank → Dw.La) b') (by
      intro x
      obtain ⟨x, rfl⟩ : ∃ x' : Fin (Vc D i).rank → Dw.La, x = fun b => Submodule.Quotient.mk (x' b) :=
        ⟨fun b => qRep (x b), funext fun b => (Classical.choose_spec (Submodule.Quotient.mk_surjective _ (x b))).symm⟩
      have e1 := (he (fun b' => x b' + H.bar s • (Pi.single b w : Fin (Vc D i).rank → Dw.La) b')).2
      have e2 := (he x).2
      simp only [RingHom.id_apply] at e1 e2
      have e3 : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t →
          Datum.redM PP (FWT.uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e
            fun b' => ι (x b' + H.bar s • (Pi.single b w : Fin (Vc D i).rank → Dw.La) b')) =
          Datum.redM PP (FWT.uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e fun b' => ι (x b')) := by
        intro PP hP
        have e4 : (fun b' => ι (x b' + H.bar s • (Pi.single b w : Fin (Vc D i).rank → Dw.La) b')) =
            fun b' => ι (x b') + ((H.bar s : 𝓞 D.host.E) : D.host.E) •
              ι ((Pi.single b w : Fin (Vc D i).rank → Dw.La) b') := by
          funext b'
          rw [map_add (f := _), map_smul]
          rfl
        rw [e4, uMat_add_smul, sig_bar]
        exact redM_add_smul PP _ _ (he x).1 (he _).1 s (hs PP hP)
      rw [omegaK_congr _ _ _ (fun PP hP => e3 PP (Or.inl hP)),
        omegaQ_congr _ _ _ _ _ _ (fun PP hP => e3 PP (Or.inr hP)), ← e2] at e1
      exact e1)
    unfold Formalism.L2.Pj.pairL at h1
    rw [Finset.sum_eq_single b] at h1
    · simpa [Dw.adj, LevelPairing.bar_bar] using h1
    · intro j _ hj; simp [Pi.single_eq_of_ne hj]
    · simp
  obtain ⟨z, hz⟩ := LevelPairing.exists_eq_smul_of_dvd (s • (cSep l₂ • levRep (q b))) l₂.M hM (fun y => by
    have h2 := Dw.alt (y + s • (cSep l₂ • levRep (q b)))
    simp only [map_add (f := _), LinearMap.add_apply, Dw.alt, zero_add, add_zero] at h2
    have h3 := hdvd y
    have : Dw.EF (s • (cSep l₂ • levRep (q b))) y = -Dw.EF y (s • (cSep l₂ • levRep (q b))) := by linarith
    rw [this]; exact h3.neg_right)
  exact ⟨z, by rw [hz, natCast_zsmul]⟩

end

end GlobalTheory.HatInt
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx.BoundedDen

theorem den_factorization_le (p : ℕ) [Fact p.Prime] (q : ℚ) (M : ℕ) (hM : 0 < M) (k : ℤ) (e : ℕ)
    (h : q * ((M : ℚ) * (p : ℚ) ^ e) = k) (ℓ : ℕ) (hℓ : ℓ ≠ p) :
    q.den.factorization ℓ ≤ M.factorization ℓ := by
  have hp : p.Prime := Fact.out
  have hN : ((M * p ^ e : ℕ) : ℚ) ≠ 0 := by
    have : 0 < M * p ^ e := Nat.mul_pos hM (pow_pos hp.pos e)
    exact_mod_cast this.ne'
  have hq : q = Rat.divInt k ((M * p ^ e : ℕ) : ℤ) := by
    rw [Rat.divInt_eq_div]
    push_cast at hN ⊢
    rw [eq_div_iff hN]; exact h
  have hd : q.den ∣ M * p ^ e := by
    have := Rat.den_dvd k ((M * p ^ e : ℕ) : ℤ)
    rw [← hq] at this
    exact_mod_cast this
  have hle := (Nat.factorization_le_iff_dvd q.den_nz (Nat.mul_pos hM (pow_pos hp.pos e)).ne').2 hd ℓ
  rw [Nat.factorization_mul hM.ne' (pow_pos hp.pos e).ne', Nat.factorization_pow, hp.factorization] at hle
  simpa [Finsupp.single_apply, Ne.symm hℓ] using hle

end GlobalTheory.LKCx.BoundedDen

namespace GlobalTheory.LKCx.BoundedDen

theorem main : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t) (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (h₁ : G.GAf), ∃ D : ℕ, 0 < D ∧ ∀ y : grp G β, f (h₁⁻¹ * toAfF G β x t hx y * h₁) ≠ 0 → ∀ ℓ : ℕ, ℓ ≠ p → (∀ i, ((Module.finBasis ℚ G.C).repr (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) i).den.factorization ℓ ≤ D.factorization ℓ) ∧ (((((y : G.Cˣ × ℚˣ).2)⁻¹ : ℚˣ) : ℚ)).den.factorization ℓ ≤ D.factorization ℓ := by
  intro p _ G β x t hx L f hf h₁
  obtain ⟨Ω, Ω', hΩ, hΩ', hmem⟩ := exists_compact_toAfF p G L f hf β x t hx h₁
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩
  let b := Module.finBasis ℚ G.C
  let b' := b.baseChange (AfP p)
  have hcpt : ∀ i, IsCompact ((b'.coord i) '' Ω) := fun i =>
    hΩ.image (IsModuleTopology.continuous_of_linearMap (b'.coord i))
  choose m hm0 hm using fun i => GlobalTheory.DenAway.den_bounded_of_isCompact p _ (hcpt i)
  obtain ⟨M', hM'0, hM'⟩ := GlobalTheory.DenAway.den_bounded_of_isCompact p Ω' hΩ'
  refine ⟨(∏ i, m i) * M', Nat.mul_pos (Finset.prod_pos fun i _ => hm0 i) hM'0, fun y hy ℓ hℓ => ⟨fun i => ?_, ?_⟩⟩
  · have hval : b'.coord i (inC G (AfP p) (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) =
        algebraMap ℚ (AfP p) (b.repr (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) i) := by
      simp only [inC, b', RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply, Module.Basis.coord_apply,
        Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]
    obtain ⟨k, e, hk⟩ := hm i (b.repr (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) i) (by rw [← hval]; exact ⟨_, (hmem y hy).1, rfl⟩)
    have h1 := den_factorization_le p _ (m i) (hm0 i) k e hk ℓ hℓ
    have hd : m i ∣ (∏ j, m j) * M' := (Finset.dvd_prod_of_mem m (Finset.mem_univ i)).mul_right _
    exact h1.trans ((Nat.factorization_le_iff_dvd (hm0 i).ne'
      (Nat.mul_pos (Finset.prod_pos fun i _ => hm0 i) hM'0).ne').2 hd ℓ)
  · have e0 : ((((y : G.Cˣ × ℚˣ).2)⁻¹ : ℚˣ) : ℚ) = (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ)⁻¹ := Units.val_inv_eq_inv_val _
    obtain ⟨k, e, hk⟩ := hM' _ (hmem y hy).2
    rw [e0]
    have h1 := den_factorization_le p _ M' hM'0 k e hk ℓ hℓ
    exact h1.trans ((Nat.factorization_le_iff_dvd hM'0.ne'
      (Nat.mul_pos (Finset.prod_pos fun i _ => hm0 i) hM'0).ne').2 (dvd_mul_left _ _) ℓ)

end GlobalTheory.LKCx.BoundedDen
end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.regular_elements_bounded_padic : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (β : G.Cˣ) (h₂ : Gr G 1), ∃ (B : ℝ) (e : ℕ), ∀ y : grp G β, f' (h₂⁻¹ * toP1 G β y * h₂) ≠ 0 → (∀ (w : Fin G.m) (a b : Fin G.n), ‖((G.rho w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) a b : G.Fw w) : PadicAlgCl p)‖ ≤ B ∧ ‖((G.rho w (sh G (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) a b : G.Fw w) : PadicAlgCl p)‖ ≤ B) ∧ ∃ (k : ℤ) (m : ℕ), ¬ p ∣ m ∧ (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ)⁻¹ * (p : ℚ) ^ e = k / m := by
  first | (exact @GlobalTheory.FixBound.bounded_of_support) | (exact GlobalTheory.FixBound.bounded_of_support) | (intros; apply GlobalTheory.FixBound.bounded_of_support <;> assumption)
end
