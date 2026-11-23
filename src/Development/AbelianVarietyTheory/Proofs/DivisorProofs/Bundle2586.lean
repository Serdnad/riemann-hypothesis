module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2583
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1364
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1923
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1884
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1459
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1200
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1500
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1564
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1223
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1493
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2574
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1222
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1224
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2352
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2486
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2582
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1910
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RatInvTheta

theorem inclR_inj (D : D7) : Function.Injective (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) :=
  Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)

theorem sigR_inclR (D : D7) (e : D.host.E) :
    sigR (AF D.host.F) D.sp.cm.sig (inclR (F := D.host.F) (AF D.host.F) e) =
      inclR (F := D.host.F) (AF D.host.F) (D.sp.cm.sig e) := by
  simp [sigR, inclR]

theorem mem_GQ_of {D : D7} (V : HSp D) (g : GA D V) (z : GL (Fin V.rank) D.host.E)
    (hz : mt V g = (z : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (F := D.host.F) (AF D.host.F))) :
    g ∈ GQ V := by
  refine ⟨z, ?_, Units.ext ?_⟩
  · have hm : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (mt V g) * JR (AF D.host.F) V.gram * mt V g =
        JR (AF D.host.F) V.gram := g.2
    have hcT : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig)
        ((z : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (F := D.host.F) (AF D.host.F))) =
        (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (z : Matrix (Fin V.rank) (Fin V.rank) D.host.E)).map
          (inclR (F := D.host.F) (AF D.host.F)) := by
      ext i j; exact sigR_inclR D _
    rw [hz, hcT] at hm
    show Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (z : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram *
      (z : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = V.gram
    apply Matrix.map_injective (inclR_inj D)
    dsimp only
    rw [Matrix.map_mul, Matrix.map_mul]
    exact hm
  · exact hz.symm

theorem thetaSum_rat_inv : ∀ {D : D7} {a a' : ℕ} (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a') (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W), IsTriple Bs Γ X om om' →
    ∀ γ ∈ ratU D.sp.cm.sig Γ.V.J, ∀ γ' ∈ ratU D.sp.cm.sig Γ.W.J, ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin a × Fin (a + a')),
      GlobalTheory.WeilM.thetaSum D.host.F (om (γ, γ') Φ) = GlobalTheory.WeilM.thetaSum D.host.F Φ := by
  intro D a a' Bs Γ X om om' hT γ hγ γ' hγ' Φ hΦ
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.hermitianSelfDualLatticeSpace_form_hermitian_nondeg_unimodular D Bs hT.base a Γ.V _ _ hT.geo.hV
  obtain ⟨hJ, L, hL, h4, h5, h6⟩ := GlobalTheory.T.skewHermitian_neg_traceZero_inv_hermitian_unimodular D Bs hT.base (a + a') Γ.W _ _ hT.geo.hW
  have hξ : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  let T := GlobalTheory.WeilSchrodinger.hspOf D Γ.V.Jᵀ h1 h2 Γ.V.L hT.geo.hV.lat.toIsLattice h3 (fun _ => (a - Γ.p, Γ.p))
  let S := GlobalTheory.WeilSchrodinger.hspOf D (-D.host.xi0 • Γ.W.J⁻¹) h4 h5 L hL h6
    (fun _ => (Γ.p + Γ.q, a + a' - (Γ.p + Γ.q)))
  have eA : Γ.V.J = T.gramᵀ := by rw [GlobalTheory.WeilSchrodinger.gram_hspOf]; rfl
  have eB : (-1 : AF D.host.F ⊗[D.host.F] D.host.E) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • S.gram⁻¹) := by
    rw [GlobalTheory.WeilSchrodinger.gram_hspOf]
    have e1 : (-D.host.xi0 • Γ.W.J⁻¹)⁻¹ = (-D.host.xi0)⁻¹ • Γ.W.J := Matrix.inv_eq_left_inv (by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_nonsing_inv _ hJ,
        inv_mul_cancel₀ (neg_ne_zero.2 hξ), one_smul])
    have e2 : D.host.xi0 • (-D.host.xi0)⁻¹ • Γ.W.J = -Γ.W.J := by
      rw [smul_smul, inv_neg, mul_neg, mul_inv_cancel₀ hξ, neg_one_smul]
    show (-1 : AF D.host.F ⊗[D.host.F] D.host.E) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • (-D.host.xi0 • Γ.W.J⁻¹)⁻¹)
    rw [e1, e2]
    funext i j
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
  have hcW : GlobalTheory.LFun.IsHecke D.host.F D.host.E (X.β / X.α) :=
    ⟨hT.chars.heckeβ.1.div' hT.chars.heckeα.1, fun x => by
      rw [MonoidHom.div_apply, hT.chars.heckeβ.2 x, hT.chars.heckeα.2 x, div_one]⟩
  have rW : GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range (X.β / X.α)
      (a + a') := by
    intro x
    have e₁ := hT.chars.resβ x
    have e₂ := hT.chars.resα x
    rw [MonoidHom.div_apply, Circle.coe_div, e₁, e₂, hT.geo.even.neg_one_pow]
    split_ifs
    · simp
    · rcases Nat.even_or_odd a with h | h
      · have h' : Even a' := (Nat.even_add.mp hT.geo.even).mp h
        rw [h.neg_one_pow, h'.neg_one_pow]; simp
      · have h' : Odd a' := by
          rcases Nat.even_or_odd a' with h'' | h''
          · exact absurd ((Nat.even_add.mp hT.geo.even).mpr h'') (Nat.not_even_iff_odd.mpr h)
          · exact h''
        rw [h.neg_one_pow, h'.neg_one_pow]; simp
  obtain ⟨ω, hω, -, hth⟩ := GlobalTheory.WeilBridge.exists_theta_eq D Bs hT.base S T Γ.V Γ.W _ _ _ _ hT.geo.hV hT.geo.hW
    eA eB Γ.M hT.geo.hM X.β (X.β / X.α) hT.chars.heckeβ hcW hT.chars.resβ rW om hT.weil
  obtain ⟨g, h, hh, hg⟩ := GlobalTheory.WeilSchrodinger.match_pair D S T Γ.V.J Γ.W.J (-1) eA eB γ γ'
  obtain ⟨z, hz⟩ := hγ
  obtain ⟨z', hz'⟩ := hγ'
  have hhQ : h ∈ GQ T := by
    refine mem_GQ_of T h z ?_
    rw [hh]
    exact (congrArg Units.val hz).symm
  have hgQ : g ∈ GQ S := by
    have m1 := congrArg Matrix.transpose (Units.mul_inv z')
    have m2 := congrArg Matrix.transpose (Units.inv_mul z')
    rw [Matrix.transpose_mul, Matrix.transpose_one] at m1 m2
    let Z : GL (Fin (a + a')) D.host.E :=
      ⟨((z'⁻¹ : GL (Fin (a + a')) D.host.E) : Matrix (Fin (a + a')) (Fin (a + a')) D.host.E)ᵀ,
        ((z' : GL (Fin (a + a')) D.host.E) : Matrix (Fin (a + a')) (Fin (a + a')) D.host.E)ᵀ, m1, m2⟩
    refine mem_GQ_of S g Z ?_
    rw [hg]
    have h0 : γ'.1 = Matrix.GeneralLinearGroup.map (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) z' := hz'.symm
    show ((γ'.1)⁻¹ : GL (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E))).1ᵀ = _
    rw [h0, ← map_inv]
    rfl
  have hf :=
    GlobalTheory.T.isThetaFunction_thetaTransform_rationalDarboux D Bs.ψ (GlobalTheory.T.isStdChar_neg_one_of_standardTraceAdelicAddChar D Bs.ψ hT.base.std) S T Γ.V.J Γ.W.J (-1) eA eB (Fin T.rank × Fin S.rank) Γ.M.co
      hT.geo.hM.rat Φ hΦ
  have key := hth γ γ' g h hh hg Φ hΦ
  have e0 := GlobalTheory.WeilBridge.thetaTr_zero D Γ.M.co Bs.ψ Φ
  have e1 := hω.om_aut g hgQ h hhQ _ hf
  exact key.trans (e1.trans e0)

end GlobalTheory.RatInvTheta
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp.FBasis

theorem exists_ne_zero_mem_H (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ)
    (hX : IsArithVar p D) (P : Pair p) (hL : IsAmpleLB P.L.B) (e : ℕ) (he : 0 < e) (a b : ℤ) :
    ∃ (c : ℕ) (γ : X.functionField), γ ≠ 0 ∧ γ ∈ P.H ((e : ℤ) * c + a) b := by
  obtain ⟨M, hM⟩ := Pair.exists_rep k X p P a b
  have hLe : IsAmpleLB (P.L.pow e).B := (isAmpleLB_pow_iff hL.isLB he).2 hL
  obtain ⟨c, -, u, hu⟩ := exists_sec_finite_subset_nonzeroLocus k X p D hX M (P.L.pow e) hLe {genericPoint X}
    (Set.finite_singleton _)
  have h1 := (Pair.rep_base k X p P).1
  have h2 := Pair.rep_pow k X p P 1 0 P.L e h1
  have h3 := Pair.rep_pow k X p P _ _ _ c h2
  have hN := Pair.rep_tens k X p P a b _ _ M _ hM h3
  have e1 : a + (c : ℤ) * ((e : ℤ) * 1) = (e : ℤ) * c + a := by ring
  have e2 : b + (c : ℤ) * ((e : ℤ) * 0) = b := by ring
  rw [e1, e2] at hN
  obtain ⟨f, -, hrange, -, hloc⟩ := RepDict.rep_dict k X p P _ _ _ hN
  have hmem : f u ∈ P.H ((e : ℤ) * c + a) b := by
    have : f u ∈ Set.range f := Set.mem_range_self u
    rw [hrange] at this
    exact this
  obtain ⟨i, hi⟩ : ∃ i, genericPoint X ∈ P.L.B.U i :=
    Opens.mem_iSup.1 (P.L.isLB.cover.ge (Opens.mem_top _))
  obtain ⟨j, hj⟩ : ∃ j, genericPoint X ∈ P.A.B.U j :=
    Opens.mem_iSup.1 (P.A.isLB.cover.ge (Opens.mem_top _))
  have hU := (hloc u (genericPoint X) i j hi hj).1 (hu rfl)
  refine ⟨c, f u, fun h0 => ?_, hmem⟩
  rw [h0] at hU
  have z : P.loc ((e : ℤ) * c + a) b 0 i j = 0 := by simp [Pair.loc]
  rw [z] at hU
  have hz : ∀ x : X, ¬ UnitAt x (0 : X.functionField) := by
    rintro x ⟨w, hw, h⟩
    exact (hw.map (algebraMap _ X.functionField)).ne_zero h
  exact hz _ hU

theorem exists_linearIndependent_of_frac {K : Type} [Field K] (F : Subfield K) [FiniteDimensional F K] (R : Subring K)
    (hR : ∀ w : K, ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ w = a / b) :
    ∃ β : Fin (Module.finrank F K) → K, (∀ i, β i ∈ R) ∧ LinearIndependent F β := by
  have hS : Algebra.adjoin F (R : Set K) = ⊤ := by
    refine eq_top_iff.2 fun w _ => ?_
    obtain ⟨a, ha, b, hb, hb0, rfl⟩ := hR w
    have hbS : b ∈ Algebra.adjoin F (R : Set K) := Algebra.subset_adjoin hb
    have hinv : b⁻¹ ∈ Algebra.adjoin F (R : Set K) :=
      (Algebra.adjoin F (R : Set K)).inv_mem_of_algebraic (x := ⟨b, hbS⟩) (Algebra.IsAlgebraic.isAlgebraic (b : K))
    rw [div_eq_mul_inv]
    exact mul_mem (Algebra.subset_adjoin ha) hinv
  have hspan : Submodule.span F (R : Set K) = ⊤ := by
    have := congrArg Subalgebra.toSubmodule hS
    rw [Algebra.adjoin_eq_span, Algebra.top_toSubmodule] at this
    have hc : (Submonoid.closure (R : Set K) : Set K) = (R : Set K) := by
      exact congrArg (fun s : Submonoid K => (s : Set K)) (Submonoid.closure_eq R.toSubmonoid)
    rw [hc] at this
    exact this
  obtain ⟨s, hsR, hsspan, hli⟩ := exists_linearIndependent F (R : Set K)
  rw [hspan] at hsspan
  let B : Module.Basis s F K := Module.Basis.mk hli (by rw [Subtype.range_coe, hsspan])
  let E : s ≃ Fin (Module.finrank F K) := B.indexEquiv (Module.finBasis F K)
  refine ⟨fun i => (E.symm i : K), fun i => hsR (E.symm i).2, ?_⟩
  exact hli.comp _ E.symm.injective

end GlobalTheory.HSAmp.FBasis

namespace GlobalTheory.HSAmp

theorem exists_linearIndependent_mem_H : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k)
    (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField),
    Gens P D e x → ∀ a b : ℤ, ∃ (c : ℕ) (g : Fin (Module.finrank (ratF x) X.functionField) → X.functionField),
    (∀ i, g i ∈ P.H (e * c + a) b) ∧ LinearIndependent (ratF x) g := by
  intro k _ X _ p D hX P hL e x hx a b
  obtain ⟨hne, -, hfin⟩ := GlobalTheory.T.sectionQuotients_transcendenceBasis_basepointFree k X p D hX P hL e x hx
  obtain ⟨U, hU, hUe, -, hreg, -, hfrac, -⟩ :=
    GlobalTheory.T.nonvanishingLocus_ample_section_isAffine_model k X p D hX P hL e (x 0) hx.pos (hx.mem 0) (hne 0)
  obtain ⟨β, hβR, hβ⟩ := FBasis.exists_linearIndependent_of_frac (ratF x) (fnOf U hU).range hfrac
  obtain ⟨c₁, γ, hγ0, hγ⟩ := FBasis.exists_ne_zero_mem_H k X p D hX P hL e hx.pos a b
  have hext : ∀ i, ∀ᶠ c : ℕ in atTop, x 0 ^ c * β i ∈ P.H ((e : ℤ) * c + 0) 0 := by
    intro i
    refine GlobalTheory.T.eventually_pow_mul_mem_hermPairSections k X p D hX P e 0 0 (x 0) (β i) (hx.mem 0) (hne 0) fun z hz i' j _ _ => ?_
    have e0 : P.loc 0 0 (β i) i' j = β i := by simp [Pair.loc]
    rw [e0]
    refine (hreg (β i)).2 (hβR i) z ?_
    rw [← SetLike.mem_coe, hUe]
    exact hz
  obtain ⟨c₂, hc₂⟩ := (Filter.eventually_all.2 hext).exists
  refine ⟨c₁ + c₂, fun i => γ * x 0 ^ c₂ * β i, fun i => ?_, ?_⟩
  · have h := (NuMul.mul_mem_H_and_nu_mul k X p P _ _ _ _ γ (x 0 ^ c₂ * β i) hγ (hc₂ i)).1
    have e1 : (e : ℤ) * c₁ + a + ((e : ℤ) * c₂ + 0) = (e : ℤ) * ((c₁ + c₂ : ℕ) : ℤ) + a := by
      push_cast; ring
    rw [e1, add_zero, ← mul_assoc] at h
    exact h
  · have ht : γ * x 0 ^ c₂ ≠ 0 := mul_ne_zero hγ0 (pow_ne_zero _ (hne 0))
    exact hβ.map' (LinearMap.mulLeft (ratF x) (γ * x 0 ^ c₂))
      (LinearMap.ker_eq_bot.2 (mul_right_injective₀ ht))

end GlobalTheory.HSAmp
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PDForm

universe u

section Gen

variable {C : Type u} [Category.{0} C]

theorem cx_H1_mk_eq_zero_iff (K : Cx C) (x : K.Z1) :
    (QuotientAddGroup.mk x : K.H1) = 0 ↔ ∃ g, K.D0 g = x.1 := by
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range]

theorem cx_H2_mk_eq_zero_iff (K : Cx C) (x : K.Z2) :
    (QuotientAddGroup.mk x : K.H2) = 0 ↔ ∃ g, K.D1 g = x.1 := by
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range]

variable {R : Type} [CommRing R] (F : C ⥤ CommAlgCat.{0} R)

theorem single1_mem (f : GlobalTheory.CatCoh.Z1 F) :
    ((f.1 : (Coef.ofAlg F).c1), (fun _ ↦ PUnit.unit : (Coef.zero C).c0)) ∈ (Cx.single (Coef.ofAlg F)).Z1 := by
  show Cx.D1 _ _ = 0
  refine Prod.ext ?_ (Prod.ext (funext fun _ ↦ funext fun _ ↦ funext fun _ ↦ rfl) (funext fun _ ↦ rfl))
  funext T T' T'' φ ψ
  have := f.2 φ ψ
  change (mp F ψ) (f.1 T T' φ) - f.1 T T'' (φ ≫ ψ) + f.1 T' T'' ψ = 0
  rw [this]; abel

theorem single_H1_mk_eq_zero_iff (x : (Cx.single (Coef.ofAlg F)).Z1) :
    (QuotientAddGroup.mk x : (Cx.single (Coef.ofAlg F)).H1) = 0 ↔ ∃ g, GlobalTheory.CatCoh.d0 F g = x.1.1 := by
  rw [cx_H1_mk_eq_zero_iff]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, by rw [← hg]; rfl⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, Prod.ext (by rw [← hg]; rfl) (Subsingleton.elim _ _)⟩

end Gen

section Gen2

variable {C : Type u} [Category.{0} C] {R : Type} [CommRing R] (F : C ⥤ CommAlgCat.{0} R)

theorem single_fst_mem_Z1 (x : (Cx.single (Coef.ofAlg F)).Z1) : x.1.1 ∈ GlobalTheory.CatCoh.Z1 F := by
  intro T T' T'' φ ψ
  have h : Cx.D1 _ x.1 = 0 := x.2
  have := congrArg (fun c ↦ c.1 T T' T'' φ ψ) h
  change (mp F ψ) (x.1.1 T T' φ) - x.1.1 T T'' (φ ≫ ψ) + x.1.1 T' T'' ψ = 0 at this
  linear_combination -this

theorem single2_mem (z : GlobalTheory.CatCoh.Z2 F) :
    ((z.1 : (Coef.ofAlg F).c2), (fun _ _ _ ↦ PUnit.unit : (Coef.zero C).c1), (fun _ ↦ PUnit.unit : (Coef.zero C).c0))
      ∈ (Cx.single (Coef.ofAlg F)).Z2 :=
  ⟨fun T T' T'' T''' φ ψ χ ↦ z.2 φ ψ χ, fun _ _ _ _ _ ↦ Subsingleton.elim _ _, fun _ _ _ ↦ Subsingleton.elim _ _,
    fun _ ↦ Subsingleton.elim _ _⟩

theorem single_fst_mem_Z2 (x : (Cx.single (Coef.ofAlg F)).Z2) : x.1.1 ∈ GlobalTheory.CatCoh.Z2 F :=
  fun _ _ _ _ φ ψ χ ↦ x.2.1 _ _ _ _ φ ψ χ

theorem single_H2_mk_eq_zero_iff (x : (Cx.single (Coef.ofAlg F)).Z2) :
    (QuotientAddGroup.mk x : (Cx.single (Coef.ofAlg F)).H2) = 0 ↔ ∃ g, GlobalTheory.CatCoh.d1 F g = x.1.1 := by
  rw [cx_H2_mk_eq_zero_iff]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g.1, by rw [← hg]; rfl⟩
  · rintro ⟨g, hg⟩
    exact ⟨(g, fun _ ↦ PUnit.unit), Prod.ext (by rw [← hg]; rfl) (Subsingleton.elim _ _)⟩

end Gen2

section Lift

variable {D : Data} (Λ : Lift D)

theorem smoothLiftThickenings_restrictionOne_sub {k k' : ((KK D.κ D.t).res Λ.L).T1} {w w' : Tot1 (OAff D.s)} (h : Λ.Res1 k w)
    (h' : Λ.Res1 k' w') : Λ.Res1 (k - k') (w - w') := by
  refine ⟨fun U V a ↦ ?_, fun U ↦ ?_⟩
  · simp only [Prod.fst_sub, Pi.sub_apply, h.1 U V a, h'.1 U V a, map_sub]
  · simp only [Prod.snd_sub, Pi.sub_apply, h.2 U, h'.2 U, map_sub, Submodule.Quotient.mk_sub]

theorem smoothLiftThickenings_restrictionTwo_sub {k k' : ((KK D.κ D.t).res Λ.L).T2} {w w' : Tot2 (OAff D.s)} (h : Λ.Res2 k w)
    (h' : Λ.Res2 k' w') : Λ.Res2 (k - k') (w - w') := by
  refine ⟨fun U V W a b ↦ ?_, fun U V a ↦ ?_, fun U ↦ ?_⟩
  · simp only [Prod.fst_sub, Pi.sub_apply, h.1 U V W a b, h'.1 U V W a b, map_sub]
  · simp only [Prod.fst_sub, Prod.snd_sub, Pi.sub_apply, h.2.1 U V a, h'.2.1 U V a, map_sub,
      Submodule.Quotient.mk_sub]
  · simp only [Prod.snd_sub, Pi.sub_apply, h.2.2 U, h'.2.2 U, map_sub, Submodule.Quotient.mk_sub]

end Lift

section Main

variable (D : Data) (Λ : Lift D)

theorem crystallineCechDeRham_degreeOne_relation_total : (∀ c, ∃ h, Λ.Rel1 c h) ∧ (∀ h, ∃ c, Λ.Rel1 c h) ∧
    ∀ c h, Λ.Rel1 c h → (c = 0 ↔ h = 0) := by
  have hfn := (GlobalTheory.T.fnMap_pullbackBijective12_kk_and_res D.R D.I D.κ D.X₀ D.t D.X D.i).1.1
  have hres := (GlobalTheory.T.lift_restriction_bijective_low_degrees D Λ).1
  obtain ⟨hW, hK, hZ⟩ := GlobalTheory.T.compatibleFormsCochains_eq_deRhamCochains_smoothLift.1 D Λ
  have key : ∀ k : (KK D.κ D.t).Z1, (∃ g, GlobalTheory.CatCoh.d0 (O D.κ D.t) g = k.1.1) ↔
      ∃ g, ((KK D.κ D.t).res Λ.L).D0 g = ((KK D.κ D.t).resMap Λ.L).p1 k.1 := fun k ↦ by
    have e := (map_eq_zero_iff _ hfn.1 (x := (QuotientAddGroup.mk k : (KK D.κ D.t).H1))).trans
      (map_eq_zero_iff _ hres.1).symm
    exact ((single_H1_mk_eq_zero_iff (O D.κ D.t) ((KK D.κ D.t).fnMap.z1 k)).symm.trans e).trans
      (cx_H1_mk_eq_zero_iff _ (((KK D.κ D.t).resMap Λ.L).z1 k))
  refine ⟨fun c ↦ ?_, fun h ↦ ?_, ?_⟩
  · obtain ⟨f, rfl⟩ := GlobalTheory.CatCoh.H1.mk_surjective _ c
    obtain ⟨x, hx⟩ := hfn.2 (QuotientAddGroup.mk ⟨_, single1_mem (O D.κ D.t) f⟩)
    obtain ⟨k, rfl⟩ := QuotientAddGroup.mk_surjective x
    obtain ⟨g, hg⟩ := (single_H1_mk_eq_zero_iff (O D.κ D.t) ((KK D.κ D.t).fnMap.z1 k - ⟨_, single1_mem _ f⟩)).1
      (by rw [QuotientAddGroup.mk_sub]; exact sub_eq_zero.2 hx)
    obtain ⟨w, hw, -⟩ := hW (((KK D.κ D.t).resMap Λ.L).p1 k.1)
    have hwZ : w ∈ cechDeRhamTotalCocyclesOne (OAff D.s) := ((hZ _ _ hw).1).1 (((KK D.κ D.t).resMap Λ.L).z1 k).2
    refine ⟨Hyp1.mk _ ⟨w, hwZ⟩, k, ⟨k.1.1, single_fst_mem_Z1 _ ((KK D.κ D.t).fnMap.z1 k)⟩, ⟨w, hwZ⟩, ?_, rfl, rfl, hw⟩
    rw [← sub_eq_zero, ← map_sub, GlobalTheory.CatCoh.H1.mk_eq_zero]
    exact ⟨g, hg⟩
  · obtain ⟨w, rfl⟩ := Hyp1.mk_surjective _ h
    obtain ⟨k0, hk0, -⟩ := hK w.1
    have hk0Z : k0 ∈ ((KK D.κ D.t).res Λ.L).Z1 := ((hZ _ _ hk0).1).2 w.2
    obtain ⟨x, hx⟩ := hres.2 (QuotientAddGroup.mk ⟨k0, hk0Z⟩)
    obtain ⟨k, rfl⟩ := QuotientAddGroup.mk_surjective x
    obtain ⟨g, hg⟩ := (cx_H1_mk_eq_zero_iff _ (((KK D.κ D.t).resMap Λ.L).z1 k - ⟨k0, hk0Z⟩)).1
      (by rw [QuotientAddGroup.mk_sub]; exact sub_eq_zero.2 hx)
    obtain ⟨w1, hw1, -⟩ := hW (((KK D.κ D.t).resMap Λ.L).p1 k.1)
    have hw1Z : w1 ∈ cechDeRhamTotalCocyclesOne (OAff D.s) := ((hZ _ _ hw1).1).1 (((KK D.κ D.t).resMap Λ.L).z1 k).2
    obtain ⟨g', hg'⟩ := (hZ _ _ (smoothLiftThickenings_restrictionOne_sub Λ hw1 hk0)).2.1 ⟨g, hg⟩
    refine ⟨GlobalTheory.CatCoh.H1.mk _ ⟨k.1.1, single_fst_mem_Z1 _ ((KK D.κ D.t).fnMap.z1 k)⟩, k, _, ⟨w1, hw1Z⟩, rfl, ?_,
      rfl, hw1⟩
    rw [← sub_eq_zero, ← map_sub, Hyp1.mk_eq_zero]
    exact ⟨g', hg'⟩
  · rintro c h ⟨k, f, w, rfl, rfl, hkf, hR⟩
    rw [GlobalTheory.CatCoh.H1.mk_eq_zero, Hyp1.mk_eq_zero, ← hkf]
    exact (key k).trans (hZ _ _ hR).2



theorem crystallineCechDeRham_degreeTwo_relation_total : (∀ c, ∃ h, Λ.Rel2 c h) ∧ (∀ h, ∃ c, Λ.Rel2 c h) ∧
    ∀ c h, Λ.Rel2 c h → (c = 0 ↔ h = 0) := by
  have hfn := (GlobalTheory.T.fnMap_pullbackBijective12_kk_and_res D.R D.I D.κ D.X₀ D.t D.X D.i).1.2
  have hres := (GlobalTheory.T.lift_restriction_bijective_low_degrees D Λ).2
  obtain ⟨hW, hK, hZ⟩ := GlobalTheory.T.compatibleFormsCochains_eq_deRhamCochains_smoothLift.2 D Λ
  have key : ∀ k : (KK D.κ D.t).Z2, (∃ g, GlobalTheory.CatCoh.d1 (O D.κ D.t) g = k.1.1) ↔
      ∃ g, ((KK D.κ D.t).res Λ.L).D1 g = ((KK D.κ D.t).resMap Λ.L).p2 k.1 := fun k ↦ by
    have e := (map_eq_zero_iff _ hfn.1 (x := (QuotientAddGroup.mk k : (KK D.κ D.t).H2))).trans
      (map_eq_zero_iff _ hres.1).symm
    exact ((single_H2_mk_eq_zero_iff (O D.κ D.t) ((KK D.κ D.t).fnMap.z2 k)).symm.trans e).trans
      (cx_H2_mk_eq_zero_iff _ (((KK D.κ D.t).resMap Λ.L).z2 k))
  refine ⟨fun c ↦ ?_, fun h ↦ ?_, ?_⟩
  · obtain ⟨f, rfl⟩ := GlobalTheory.CatCoh.H2.mk_surjective _ c
    obtain ⟨x, hx⟩ := hfn.2 (QuotientAddGroup.mk ⟨_, single2_mem (O D.κ D.t) f⟩)
    obtain ⟨k, rfl⟩ := QuotientAddGroup.mk_surjective x
    obtain ⟨g, hg⟩ := (single_H2_mk_eq_zero_iff (O D.κ D.t) ((KK D.κ D.t).fnMap.z2 k - ⟨_, single2_mem _ f⟩)).1
      (by rw [QuotientAddGroup.mk_sub]; exact sub_eq_zero.2 hx)
    obtain ⟨w, hw, -⟩ := hW (((KK D.κ D.t).resMap Λ.L).p2 k.1)
    have hwZ : w ∈ cechDeRhamTotalCocyclesTwo (OAff D.s) := ((hZ _ _ hw).1).1 (((KK D.κ D.t).resMap Λ.L).z2 k).2
    refine ⟨Hyp2.mk _ ⟨w, hwZ⟩, k, ⟨k.1.1, single_fst_mem_Z2 _ ((KK D.κ D.t).fnMap.z2 k)⟩, ⟨w, hwZ⟩, ?_, rfl, rfl, hw⟩
    rw [← sub_eq_zero, ← map_sub, GlobalTheory.CatCoh.H2.mk_eq_zero]
    exact ⟨g, hg⟩
  · obtain ⟨w, rfl⟩ := Hyp2.mk_surjective _ h
    obtain ⟨k0, hk0, -⟩ := hK w.1
    have hk0Z : k0 ∈ ((KK D.κ D.t).res Λ.L).Z2 := ((hZ _ _ hk0).1).2 w.2
    obtain ⟨x, hx⟩ := hres.2 (QuotientAddGroup.mk ⟨k0, hk0Z⟩)
    obtain ⟨k, rfl⟩ := QuotientAddGroup.mk_surjective x
    obtain ⟨g, hg⟩ := (cx_H2_mk_eq_zero_iff _ (((KK D.κ D.t).resMap Λ.L).z2 k - ⟨k0, hk0Z⟩)).1
      (by rw [QuotientAddGroup.mk_sub]; exact sub_eq_zero.2 hx)
    obtain ⟨w1, hw1, -⟩ := hW (((KK D.κ D.t).resMap Λ.L).p2 k.1)
    have hw1Z : w1 ∈ cechDeRhamTotalCocyclesTwo (OAff D.s) := ((hZ _ _ hw1).1).1 (((KK D.κ D.t).resMap Λ.L).z2 k).2
    have hR : Λ.Res2 (((KK D.κ D.t).resMap Λ.L).p2 k.1 - k0) (w1 - w.1) := smoothLiftThickenings_restrictionTwo_sub Λ hw1 hk0
    have hE := ((hZ _ _ hR).2).1
    obtain ⟨g', hg'⟩ := hE ⟨g, by rw [hg, AddSubgroup.coe_sub]; rfl⟩
    refine ⟨GlobalTheory.CatCoh.H2.mk _ ⟨k.1.1, single_fst_mem_Z2 _ ((KK D.κ D.t).fnMap.z2 k)⟩, k, _, ⟨w1, hw1Z⟩, rfl, ?_,
      rfl, hw1⟩
    rw [← sub_eq_zero, ← map_sub, Hyp2.mk_eq_zero]
    exact ⟨g', hg'⟩
  · rintro c h ⟨k, f, w, rfl, rfl, hkf, hR⟩
    rw [GlobalTheory.CatCoh.H2.mk_eq_zero, Hyp2.mk_eq_zero, ← hkf]
    exact (key k).trans (hZ _ _ hR).2

end Main

theorem rel_total_zero : (∀ (D : Data) (Λ : Lift D), (∀ c, ∃ h, Λ.Rel1 c h) ∧ (∀ h, ∃ c, Λ.Rel1 c h) ∧
    ∀ c h, Λ.Rel1 c h → (c = 0 ↔ h = 0)) ∧ ∀ (D : Data) (Λ : Lift D), (∀ c, ∃ h, Λ.Rel2 c h) ∧
    (∀ h, ∃ c, Λ.Rel2 c h) ∧ ∀ c h, Λ.Rel2 c h → (c = 0 ↔ h = 0) :=
  ⟨crystallineCechDeRham_degreeOne_relation_total, crystallineCechDeRham_degreeTwo_relation_total⟩

end GlobalTheory.PDForm
end
end
