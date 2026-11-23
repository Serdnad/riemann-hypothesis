module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2429
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle212
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle197
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle205
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle160
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1174
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle860
import Formalism.GradedWeylDivisibility.FinalD
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin

@[expose] public section

section

open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open Formalism.CohomologicalDescent.DepthNonnegative (NablaT)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem UpperTheory.sum_eq_of_dual_sums {G ι κ : Type} {M : Type} [AddCommGroup M] [Module ℂ M] (R : Finset ι) (B : Finset κ)
    (u : ι → G) (v : κ → G) (Fm : G → M)
    (h : ∀ ℓ : Module.Dual ℂ M, ∑ a ∈ B, ℓ (Fm (v a)) = ∑ γ ∈ R, ℓ (Fm (u γ))) :
    ∑ γ ∈ R, Fm (u γ) = ∑ a ∈ B, Fm (v a) := by
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro ℓ

  rw [map_sub, map_sum, map_sum, sub_eq_zero]
  exact (h ℓ).symm

private theorem UpperTheory.dual_invariant_of_trivial_character {G : Type} [Group G] {M : Type} [AddCommGroup M] [Module ℂ M] (J : Subgroup G) (χ : J →* ℂˣ)
    (Fm : G → M) (hF : ∀ (κ : J) g, Fm (g * κ) = ((χ κ : ℂˣ) : ℂ) • Fm g) (ℓ : Module.Dual ℂ M) (g : G) (k : J)
    (hk : χ k = 1) : ℓ (Fm (g * k)) = ℓ (Fm g) := by
  rw [hF, hk, Units.val_one, one_smul]

private theorem UpperTheory.hecke_single_eq_sum {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ)
    (F : Bridge.Gf V → ℂ) (g : Bridge.Gf V) :
    GlobalTheory.Hk3.hkF V P (Finsupp.single d 1) F g =
      ∑ γ ∈ GlobalTheory.Hk3.rep V P d, F (g * (Formalism.L2.Theta.finHom V).rangeRestrict γ) := by
  have e1 : GlobalTheory.Hk3.hkF V P (Finsupp.single d 1) F g =
      (1 : ℂ) • ∑ γ ∈ GlobalTheory.Hk3.rep V P d, F (g * (Formalism.L2.Theta.finHom V).rangeRestrict γ) :=
    Finsupp.sum_single_index
      (h := fun d (z : ℂ) => z • ∑ γ ∈ GlobalTheory.Hk3.rep V P d, F (g * (Formalism.L2.Theta.finHom V).rangeRestrict γ))
      (zero_smul ℂ _)
  exact e1.trans (one_smul ℂ _)

private theorem UpperTheory.level_character_trivial {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))
    (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)
    (hc' : Formalism.IndefR.Lev.IsBaseFrame V β Λ 1) (P : HeightOneSpectrum (𝓞 D.host.E))
    (h1 : ((1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal)
    (hoff : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P) :
    ∀ y : (levEnv V β L).J, GlobalTheory.Hk3.IsLocElt V P y → (levEnv V β L).χ y = 1 := by
  have hl := fun e f' he => (GlobalTheory.LevSplit.lev_split V β Λ 1 (Formalism.IndefR.Lev.flag1L L) hc').2 P e f' he h1 hoff
  rintro ⟨y, hy⟩ ⟨e, f', a, he, ha, hxa, hs⟩
  obtain rfl : y = (Formalism.L2.Theta.finHom V).rangeRestrict a := Subtype.ext hxa
  exact Units.ext ((hl e f' he).2.1 a ⟨ha, hy⟩ hs)

private theorem UpperTheory.hecke_offprime_sum {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))
    (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)
    (hβ : ∃ c : ℕ, Formalism.IndefR.Lev.IsBaseFrame V β Λ (1 ^ c)) (P : HeightOneSpectrum (𝓞 D.host.E))
    (hoff : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P)
    (d : List ℤ) (x : Bridge.Gf V) (B : Finset (Bridge.Gf V)) (hd : d.Pairwise (fun a b => b ≤ a))
    (hx : GlobalTheory.Hk3.IsLabElt V P d x) (hB : ∀ a ∈ B, GlobalTheory.Hk3.IsLocElt V P a) (hDC : Bridge.IsDC (levEnv V β L).J x B) :
    ∃ R : Finset (Formalism.L2.Theta.GA D V),
      GlobalTheory.Hk3.SphOp V (Formalism.DivisionValues.conjPl P) (Formalism.IndefR.Mult.dualLab d) R ∧
      ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (Fm : Bridge.Gf V → M),
        (∀ (κ : (levEnv V β L).J) g, Fm (g * κ) = (((levEnv V β L).χ κ : ℂˣ) : ℂ) • Fm g) → ∀ g,
        ∑ γ ∈ R, Fm (g * (Formalism.L2.Theta.finHom V).rangeRestrict γ) = ∑ a ∈ B, Fm (g * a) := by
  refine hβ.elim fun c hc => ?_
  have hc' : Formalism.IndefR.Lev.IsBaseFrame V β Λ 1 := (one_pow c : (1 : ℕ) ^ c = 1) ▸ hc
  have h1 : ((1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    rw [Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
  have hχ := UpperTheory.level_character_trivial V β Λ L hc' P h1 hoff
  have H := GlobalTheory.T.doubleCosetOperator_eq_labelOperator_localReps V β Λ 1 L hc' P h1 hoff d x B hd hx hB hDC
  have hs : GlobalTheory.Hk3.SphOp V (Formalism.DivisionValues.conjPl (Formalism.DivisionValues.conjPl P)) d (GlobalTheory.Hk3.rep V P d) := by
    rw [GlobalTheory.SphConj.conjPl_conjPl]
    exact GlobalTheory.SphLabelOps.sphOp_rep H.1
  refine ⟨GlobalTheory.Hk3.rep V P d, GlobalTheory.SphConj.sphOp_conj V _ d _ hs, fun M _ _ Fm hF g => ?_⟩
  refine UpperTheory.sum_eq_of_dual_sums _ _ (fun γ => g * (Formalism.L2.Theta.finHom V).rangeRestrict γ) (fun a => g * a) Fm fun ℓ => ?_
  have h2 := H.2 ℂ (fun h => ℓ (Fm h)) (fun h k hk => UpperTheory.dual_invariant_of_trivial_character _ _ Fm hF ℓ h k (hχ k hk))
  exact (congrFun h2 g).trans (UpperTheory.hecke_single_eq_sum V P d (fun h => ℓ (Fm h)) g)

theorem UpperTheory.exists_sphericalHeckeRep_splitLabel_of_offLevelPlace :
    ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
        {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (j : Fin D.R.m) (t : p.P.T) (Q : (blk p j t).Pl) (k : ℕ), 1 ≤ k → k ≤ (Vc D j).rank →
        (∀ a ∈ hkA p j t (Q, k), GlobalTheory.Hk3.IsLocElt (Vc D j) (plOf p j t Q) a) ∧
        ∃ R : Finset (Formalism.L2.Theta.GA D (Vc D j)),
          GlobalTheory.Hk3.SphOp (Vc D j) (labOf p j t Q) (Formalism.IndefR.Mult.dualLab (Formalism.IndefR.Mult.splitLab (Vc D j).rank k)) R ∧
          ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (Fm : Bridge.Gf (Vc D j) → M),
            (∀ (κ : levJ p j t) g, Fm (g * κ) = ((levChi p j t κ : ℂˣ) : ℂ) • Fm g) → ∀ g,
            ∑ γ ∈ R, Fm (g * (Formalism.L2.Theta.finHom (Vc D j)).rangeRestrict γ) = ∑ a ∈ hkA p j t (Q, k), Fm (g * a) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p j t Q k hpos hk
  obtain ⟨hg, -, -⟩ := (GlobalTheory.GoodPrimes.good_primes p.R.toRealDat (p.P.face p.Dcf p.Spf p.Del p.h0 Csz).lv2
    p.charW.base.lev).2.2.2 p.charW.base.fam t Q.1 Q.2
  have hs := fun x => GlobalTheory.T.split_hecke_element_label_zeros_then_neg_ones (Vc D j) p.R.pl _ ((Q, k) : _ × ℕ) x
  have hloc : ∀ a ∈ hkA p j t (Q, k), GlobalTheory.Hk3.IsLocElt (Vc D j) (plOf p j t Q) a :=
    fun a ha => (hs a).2.1 ((p.R.B.L j t).hecke.hA_loc (Q, k) ⟨hpos, hk⟩ a ha)
  exact ⟨hloc, UpperTheory.hecke_offprime_sum (Vc D j) (p.R.βV j) (p.R.ΛV j) (p.R.datVt j t) (p.charW.base.lev.βV j) (plOf p j t Q) hg
    _ ((p.R.B.L j t).hecke.hx (Q, k)) (hkA p j t (Q, k)) (hs 1).2.2
    ((hs _).1 hk ((p.R.B.L j t).hecke.hx_ok (Q, k) ⟨hpos, hk⟩)) hloc ((p.R.B.L j t).hecke.hDC (Q, k) ⟨hpos, hk⟩)⟩
end

section

open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR GlobalTheory.UnitaryBC GlobalTheory.FrameAut Formalism.CohomologicalDescent.DepthNonnegative
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem UpperTheory.infinite_matrix_rational {D : D7} {V : HSp D}
    (θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ)
    (h : GA D V) (γ₀ : GL (Fin V.rank) D.host.E)
    (e : matHom V h = Matrix.GeneralLinearGroup.map (incA D) γ₀) (τ : D.what₂.Tau) :
    Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ) h =
      (Matrix.GeneralLinearGroup.map (tauE D τ) γ₀ : GL (Fin V.rank) ℂ).val := by
  have e' : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat _ D.sp.cm.sig V.gram h = Matrix.GeneralLinearGroup.map (incA D) γ₀ := e
  unfold Formalism.MainNotions.StandardLattice.infMat
  rw [e']
  ext a b
  change θ τ (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA D.host.F) (AlgHom.id D.host.F D.host.E)
    ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ⊗ₜ[D.host.F] γ₀.val a b)) = tauE D τ (γ₀.val a b)
  rw [Algebra.TensorProduct.map_tmul, map_one]
  exact (hθ τ).1 _

private theorem UpperTheory.exists_conjugate_embedding {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (σ ε : E →+* ℂ)
    (hε : ε = σ ∨ ε = ComplexEmbedding.conjugate σ) (A : Matrix (Fin n) (Fin n) ℂ) (hA : IsUnit A) :
    ∃ B : GL (Fin n) ℂ, ∀ (x : UA E n) (γ₀ : GL (Fin n) E),
      (Matrix.GeneralLinearGroup.map σ γ₀ : GL (Fin n) ℂ).val = A * (cEmb σ x : Matrix (Fin n) (Fin n) ℂ) * A⁻¹ →
      Matrix.GeneralLinearGroup.map ε γ₀ = B * cEmb ε x * B⁻¹ := by
  obtain ⟨B, rfl⟩ := hA
  have key : ∀ (x : UA E n) (γ₀ : GL (Fin n) E),
      (Matrix.GeneralLinearGroup.map σ γ₀ : GL (Fin n) ℂ).val =
        B.val * (cEmb σ x : Matrix (Fin n) (Fin n) ℂ) * (B.val)⁻¹ →
      Matrix.GeneralLinearGroup.map σ γ₀ = B * cEmb σ x * B⁻¹ := fun x γ₀ h => by
    apply Units.ext
    rw [h, Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
  rcases hε with rfl | rfl
  · exact ⟨B, key⟩
  · refine ⟨Matrix.GeneralLinearGroup.map (starRingEnd ℂ) B, fun x γ₀ h => ?_⟩
    have h1 := congrArg (Matrix.GeneralLinearGroup.map (starRingEnd ℂ)) (key x γ₀ h)
    rw [map_mul, map_mul, map_inv] at h1
    have h2 : Matrix.GeneralLinearGroup.map (starRingEnd ℂ) (cEmb σ x) = cEmb (ComplexEmbedding.conjugate σ) x := by
      ext a b
      exact (GlobalTheory.DefiniteBC.coord_conjugate σ _).symm
    rw [h2] at h1
    rw [← h1]
    ext a b
    rfl

private theorem UpperTheory.weight_operator_conjugate {n : ℕ} {ι : Type} [Fintype ι] (mu : ι → ℕ → ℕ) (sh : ι → ℤ)
    (B C G : ι → GL (Fin n) ℂ) (h : G = B * C * B⁻¹) (u : NablaT ℂ n mu) :
    wtOp ℂ n mu sh B⁻¹ (wtOp ℂ n mu sh G u) = wtOp ℂ n mu sh C (wtOp ℂ n mu sh B⁻¹ u) := by
  classical
  rw [h, ← Module.End.mul_apply, ← wtOp_mul, ← mul_assoc, inv_mul_cancel_left, wtOp_mul]
  rfl

private theorem UpperTheory.monoidHom_kernel_invariance {G H K : Type} [Monoid G] [Monoid H] [Monoid K] (j : G →* H) (φ : H →* K)
    (g x : G) (h : H) (hx : φ (j x) = 1) : φ (j (g * x) * h) = φ (j g * h) := by
  simp only [map_mul, hx, mul_one]

theorem UpperTheory.vectorValued_autForm_equivariant_infinite_component :
    ∀ (D : D7) [IsCMField D.host.E] (V : HSp D) (θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
        (j : UA D.host.E V.rank ≃ₜ* GA D V) (h₀ : GA D V), IsInfFam θ → GlobalTheory.DefTransfer.IsTransfer V θ j h₀ →
        ∀ (emb : D.what₂.Tau → (D.host.E →+* ℂ)), (∀ τ, emb τ = tauE D τ ∨ emb τ = ComplexEmbedding.conjugate (tauE D τ)) →
        ∀ (mu : D.what₂.Tau → ℕ → ℕ) (sh : D.what₂.Tau → ℤ) (Fm : Bridge.Gf V → NablaT ℂ V.rank mu), Fm ≠ 0 →
        (∀ (γ : GQ V) (γ₀ : GL (Fin V.rank) D.host.E), matHom V γ = Matrix.GeneralLinearGroup.map (incA D) γ₀ → ∀ g,
          Fm (Bridge.ratF V γ * g) = wtOp ℂ V.rank mu sh (fun τ => Matrix.GeneralLinearGroup.map (emb τ) γ₀) (Fm g)) →
        (∀ᶠ κ in nhds (1 : GA D V), ∀ g, Fm (g * (finHom V).rangeRestrict κ) = Fm g) →
        ∃ F1 : UA D.host.E V.rank → NablaT ℂ V.rank mu, F1 ≠ 0 ∧
          (∀ γ ∈ ratU D.host.E V.rank, ∀ g, F1 (γ * g) = wtOp ℂ V.rank mu sh (fun τ => cEmb (emb τ) γ) (F1 g)) ∧
          (∀ x ∈ infU D.host.E V.rank, ∀ g, F1 (g * x) = F1 g) ∧ (∀ᶠ y in nhds (1 : UA D.host.E V.rank), ∀ g, F1 (g * y) = F1 g) ∧
          ∃ A : Module.End ℂ (NablaT ℂ V.rank mu), ∀ x, F1 x = A (Fm ((finHom V).rangeRestrict (j x * h₀))) := by
  intro D _ V θ j h₀ hθ hT emb hemb mu sh Fm hF hrat hlev
  classical
  obtain ⟨-, hQ, -, hI, ⟨A, hA, hAe⟩, -⟩ := hT
  choose B hB using fun τ => UpperTheory.exists_conjugate_embedding (tauE D τ) (emb τ) (hemb τ) (A τ) (hA τ)
  refine ⟨fun x => wtOp ℂ V.rank mu sh B⁻¹ (Fm ((finHom V).rangeRestrict (j x * h₀))), ?_, ?_, ?_, ?_, _, fun _ => rfl⟩
  · intro h0
    apply hF
    funext g
    obtain ⟨k, rfl⟩ := (finHom V).rangeRestrict_surjective g
    have h1 := congrArg (wtOp ℂ V.rank mu sh B) (congrFun h0 (j.symm (k * h₀⁻¹)))
    simp only [ContinuousMulEquiv.apply_symm_apply, inv_mul_cancel_right, Pi.zero_apply, map_zero] at h1
    rw [← Module.End.mul_apply, ← wtOp_mul, mul_inv_cancel, wtOp_one] at h1
    exact h1
  · intro γ hγ g
    have hj : j γ ∈ GQ V := (hQ γ).1 hγ
    obtain ⟨γ₀, -, e⟩ := id hj
    have e' : matHom V (j γ) = Matrix.GeneralLinearGroup.map (incA D) γ₀ := e.symm
    have h1 := hrat ⟨j γ, hj⟩ γ₀ e' ((finHom V).rangeRestrict (j g * h₀))
    have h2 : (finHom V).rangeRestrict (j (γ * g) * h₀) =
        Bridge.ratF V ⟨j γ, hj⟩ * (finHom V).rangeRestrict (j g * h₀) := by
      have h4 : j (γ * g) * h₀ = j γ * (j g * h₀) := by rw [map_mul, mul_assoc]
      exact (congrArg (finHom V).rangeRestrict h4).trans (map_mul (finHom V).rangeRestrict _ _)
    have h3 : (fun τ => Matrix.GeneralLinearGroup.map (emb τ) γ₀) = B * (fun τ => cEmb (emb τ) γ) * B⁻¹ := by
      funext τ
      exact hB τ γ γ₀ ((UpperTheory.infinite_matrix_rational θ hθ _ γ₀ e' τ).symm.trans (hAe τ γ))
    exact (congrArg (wtOp ℂ V.rank mu sh B⁻¹) ((congrArg Fm h2).trans h1)).trans
      (UpperTheory.weight_operator_conjugate mu sh B _ _ h3 _)
  · intro x hx g
    have hj : finHom V (j x) = 1 := (hI x).1 hx
    have h1 : (finHom V).rangeRestrict (j x) = 1 := Subtype.ext hj
    exact congrArg (fun z => wtOp ℂ V.rank mu sh B⁻¹ (Fm z))
      (UpperTheory.monoidHom_kernel_invariance j.toMulEquiv.toMonoidHom (finHom V).rangeRestrict g x h₀ h1)
  · have hc : Continuous fun y : UA D.host.E V.rank => h₀⁻¹ * j y * h₀ :=
      (continuous_const.mul j.continuous).mul continuous_const
    have ht : Filter.Tendsto (fun y : UA D.host.E V.rank => h₀⁻¹ * j y * h₀) (nhds 1) (nhds 1) := by
      exact hc.tendsto' 1 1 (by simp only [map_one, mul_one, inv_mul_cancel])
    filter_upwards [ht.eventually hlev] with y hy g
    have h1 : j (g * y) * h₀ = j g * h₀ * (h₀⁻¹ * j y * h₀) := by
      rw [map_mul]
      group
    exact congrArg (wtOp ℂ V.rank mu sh B⁻¹) ((congrArg Fm ((congrArg (finHom V).rangeRestrict h1).trans
      (map_mul (finHom V).rangeRestrict _ _))).trans (hy _))
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.BasicNotions GlobalTheory.DefU GlobalTheory.FrameAut Formalism.CohomologicalDescent.DepthNonnegative

private theorem fd_dw (n : ℕ) (ν : Fin n → ℕ) : FiniteDimensional ℂ (Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν) := by
  obtain ⟨b, ⟨-, hb, -⟩, -⟩ := Formalism.GradedWeylDivisibility.sSBasis ℂ n n ν
  have : Finite (Formalism.GradedWeylDivisibility.ssIdx n n ν) := (Formalism.GradedWeylDivisibility.sSIdxFinite n n _).to_subtype
  rw [← hb]
  exact FiniteDimensional.span_of_finite ℂ (Set.finite_range b)

private theorem cont_rowAct (n : ℕ) (f : MvPolynomial (Fin n × Fin n) ℂ) :
    ∀ ℓ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] ℂ,
      Continuous fun g : Matrix (Fin n) (Fin n) ℂ => ℓ (Formalism.GradedWeylDivisibility.rowAct ℂ g f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    intro ℓ
    simp only [Formalism.GradedWeylDivisibility.rowAct, MvPolynomial.algHom_C]
    exact continuous_const
  | add p q hp hq =>
    intro ℓ
    simp only [map_add (f := _)]
    exact (hp ℓ).add (hq ℓ)
  | mul_X p v hp =>
    intro ℓ
    have e : ∀ g : Matrix (Fin n) (Fin n) ℂ, ℓ (Formalism.GradedWeylDivisibility.rowAct ℂ g (p * MvPolynomial.X v)) =
        ∑ b : Fin n, g v.1 b * (ℓ ∘ₗ LinearMap.mulRight ℂ (MvPolynomial.X (b, v.2))) (Formalism.GradedWeylDivisibility.rowAct ℂ g p) := by
      intro g
      have h1 : Formalism.GradedWeylDivisibility.rowAct ℂ g (MvPolynomial.X v : MvPolynomial (Fin n × Fin n) ℂ) =
          ∑ b : Fin n, MvPolynomial.C (g v.1 b) * MvPolynomial.X (b, v.2) := by
        simp only [Formalism.GradedWeylDivisibility.rowAct, MvPolynomial.aeval_X]

      rw [map_mul, h1, Finset.mul_sum, map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [mul_left_comm, ← MvPolynomial.smul_eq_C_mul, map_smul, smul_eq_mul]
      rfl
    simp only [e]
    refine continuous_finsetSum _ fun b _ => ?_
    exact (continuous_id.matrix_elem v.1 b).mul (hp _)

private theorem cont_rep (n : ℕ) (ν : Fin n → ℕ) (ℓ : Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν →ₗ[ℂ] ℂ)
    (u : Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν) :
    Continuous fun g : GL (Fin n) ℂ => ℓ (Formalism.UG.dualWeylRep ℂ n n ν g u) := by
  obtain ⟨L, hL⟩ := LinearMap.exists_extend ℓ
  have e : ∀ g : GL (Fin n) ℂ, ℓ (Formalism.UG.dualWeylRep ℂ n n ν g u) =
      L (Formalism.GradedWeylDivisibility.rowAct ℂ ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) (u : MvPolynomial (Fin n × Fin n) ℂ)) := by
    intro g
    rw [← hL, LinearMap.comp_apply, Submodule.subtype_apply, Formalism.UG.dualWeylRep_apply]
    rfl
  simp only [e]
  exact (cont_rowAct n _ L).comp Units.continuous_coe_inv

private theorem cont_multi {X ι : Type} [TopologicalSpace X] [Fintype ι] [DecidableEq ι] {V : ι → Type}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)] [∀ i, FiniteDimensional ℂ (V i)]
    (m : (∀ i, V i) →ₘₗ[ℂ] ℂ) (F : ∀ i, X → V i) (hF : ∀ i (ℓ : V i →ₗ[ℂ] ℂ), Continuous fun x => ℓ (F i x)) :
    Continuous fun x => m fun i => F i x := by
  let b := fun i => Module.finBasis ℂ (V i)
  have e : ∀ x, (m fun i => F i x) = ∑ r : ∀ i, Fin (Module.finrank ℂ (V i)),
      (∏ i, (b i).coord (r i) (F i x)) • m fun i => b i (r i) := by
    intro x
    have h1 : (fun i => F i x) = fun i => ∑ j, (b i).coord j (F i x) • b i j := by
      funext i
      simp only [Module.Basis.coord_apply, Module.Basis.sum_repr]

    rw [h1, MultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [MultilinearMap.map_smul_univ, RingHom.id_apply]
  simp only [e]
  refine continuous_finsetSum _ fun r _ => ?_
  exact (continuous_finsetProd _ fun i _ => hF i _).smul continuous_const

theorem UpperTheory.finiteDimensional_nablaT_and_continuous_wtOp :
    ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (sh : ι → ℤ),
        FiniteDimensional ℂ (NablaT ℂ n mu) ∧ ∀ (ℓ : NablaT ℂ n mu →ₗ[ℂ] ℂ) (u : NablaT ℂ n mu),
          Continuous fun g : ι → GL (Fin n) ℂ => ℓ (wtOp ℂ n mu sh g u) := by
  intro n ι _ _ mu sh
  haveI : ∀ τ, FiniteDimensional ℂ (Formalism.GradedWeylDivisibility.dualWeyl ℂ n n (Formalism.CohomologicalDescent.LD.res n (mu τ))) := fun τ => fd_dw n _
  refine ⟨Module.Finite.of_basis (Basis.piTensorProduct fun τ => Module.finBasis ℂ _), fun ℓ u => ?_⟩
  have h1 : Continuous fun g : ι → GL (Fin n) ℂ => ℓ (GlobalTheory.ExpFrame.grp ℂ n mu g u) := by
    induction u using PiTensorProduct.induction_on with
    | smul_tprod c x =>
      simp only [map_smul, GlobalTheory.SemilinTransport.grp_tprod]
      refine Continuous.const_smul ?_ c
      exact cont_multi (ℓ.compMultilinearMap (PiTensorProduct.tprod ℂ))
        (fun τ (g : ι → GL (Fin n) ℂ) => Formalism.UG.dualWeylRep ℂ n n _ (g τ) (x τ))
        (fun τ l => (cont_rep n _ l (x τ)).comp (continuous_apply τ))
    | add a b ha hb =>
      simp only [map_add (f := _)]
      exact ha.add hb
  simp only [wtOp_apply, map_smul]
  have h2 : Continuous fun g : ι → GL (Fin n) ℂ =>
      (∏ τ, Matrix.GeneralLinearGroup.det (g τ) ^ (-sh τ) : ℂˣ) := by
    refine continuous_finsetProd _ fun τ _ => ?_
    refine Continuous.zpow ?_ _
    exact Matrix.GeneralLinearGroup.continuous_det.comp (continuous_apply τ)
  exact (Units.continuous_val.comp h2).smul h1
end
