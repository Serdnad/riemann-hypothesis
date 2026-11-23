module

public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1892
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle305
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle306
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle317
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle877
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1296
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle187
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle589
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1346
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilInertPlaceVacuumEigenfunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2294
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CocInv

variable {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A]

def affVal (V : A.left.affineOpens) (P : GPt A) (h : P.In V.1) : (Pt.aff (A.hom ≫ 𝟙 (Sp K)) V).Hom P where
  ρ := { (GlobalTheory.Points.valMap P.x V.1 (show ⊤ ≤ P.x ⁻¹ᵁ V.1 from h)).hom with
    commutes' := fun r ↦
      (GlobalTheory.Points.valR_eq P.x V.1 h (constFn (A.hom ≫ 𝟙 (Sp K)) V.1 r)).symm.trans
        (GlobalTheory.Points.valR_constFn_of_over _ (algebraMap K P.B) P.x P.w V.1 h r) }
  pt := GlobalTheory.Points.specMap_valMap_fromSpec V.2 P.x h

theorem affVal_ρ (V : A.left.affineOpens) (P : GPt A) (h : P.In V.1) (f : CechDR.Sec (A.hom ≫ 𝟙 (Sp K)) V.1) :
    (affVal V P h).ρ f = valR P.x V.1 f :=
  (GlobalTheory.Points.valR_eq P.x V.1 h f).symm

theorem affVal_comp (V : A.left.affineOpens) {P Q : GPt A} (h : P.In V.1) (φ : P.Hom Q) :
    (affVal V P h).comp φ = affVal V Q (h.map φ) := by
  have e : ((affVal V P h).comp φ).ρ = (affVal V Q (h.map φ)).ρ := by
    ext f
    change φ.ρ ((affVal V P h).ρ f) = _
    rw [affVal_ρ, affVal_ρ, ← φ.pt]
    exact (GlobalTheory.Points.valR_spMap_comp (φ.ρ : P.B →+* Q.B) P.x V.1 h f).symm
  cases h1 : (affVal V P h).comp φ
  cases h2 : affVal V Q (h.map φ)
  rw [h1, h2] at e
  cases e
  rfl

theorem aff_in (V : A.left.affineOpens) : (Pt.aff (A.hom ≫ 𝟙 (Sp K)) V).In V.1 :=
  V.2.fromSpec_preimage_self.ge

def Idx {I : Type} (U : I → A.left.Opens) : Type := {p : I × A.left.affineOpens // p.2.1 ≤ U p.1}


omit [GrpObj A] in
theorem iSup_idx {I : Type} (U : I → A.left.Opens) (hU : ⨆ i, U i = ⊤) : ⨆ a : Idx U, a.1.2.1 = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ ⨆ i, U i := hU.ge trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    A.left.isBasis_affineOpens.exists_subset_of_mem_open hi (U i).2
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(i, ⟨V, hV⟩), hVU⟩, hxV⟩


open Classical in
def βa {I : Type} {U : I → A.left.Opens} (β : ∀ P Q : GPt A, P.Hom Q → Q.B) (a : Idx U) :
    PtFn (A.hom ≫ 𝟙 (Sp K)) :=
  fun P ↦ if h : P.In a.1.2.1 then β _ P (affVal a.1.2 P h) else 0

theorem βa_step {I : Type} {U : I → A.left.Opens} {β : ∀ P Q : GPt A, P.Hom Q → Q.B}
    (hβ : ∀ (P Q T : GPt A) (φ : P.Hom Q) (ψ : Q.Hom T), (∃ i, P.In (U i)) →
      β P T (φ.comp ψ) = ψ.ρ (β P Q φ) + β Q T ψ) (a : Idx U) {P Q : GPt A} (h : P.In a.1.2.1)
    (φ : P.Hom Q) : βa β a Q = φ.ρ (βa β a P) + β P Q φ := by
  have hQ : Q.In a.1.2.1 := h.map φ
  simp only [βa, dif_pos h, dif_pos hQ]
  rw [← affVal_comp a.1.2 h φ]
  exact hβ _ P Q _ φ ⟨a.1.1, (aff_in a.1.2).mono a.2⟩


open Classical in
theorem exists_coboundary_snd_tr : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (I : Type) (U : I → A.left.Opens), ⨆ i, U i = ⊤ → ∀ β : ∀ P Q : GPt A, P.Hom Q → Q.B, (∀ (P Q T : GPt A) (φ : P.Hom Q) (ψ : Q.Hom T), (∃ i, P.In (U i)) → β P T (φ.comp ψ) = ψ.ρ (β P Q φ) + β Q T ψ) → ∀ v : epsR K ⟶ A, IsTangent v → ∃ G : PtFn (A.hom ≫ 𝟙 (Sp K)), ∀ (i : I) (V : A.left.affineOpens), V.1 ≤ U i → ∀ (P Q : GPt A) (φ : P.Hom Q), P.In V.1 → TrivSqZeroExt.snd (R := Q.B) (β (P.tr v) (Q.tr v) (φ.tr v)) = G Q - φ.ρ (G P) := by
  intro K _ A _ hA I U hU β hβ v hv
  let W : Idx U → A.left.Opens := fun a ↦ a.1.2.1

  have hsec : ∀ a b : Idx U, ∃ f : Γ(A.left, W a ⊓ W b), ∀ P : GPt A, P.In (W a ⊓ W b) →
      βa β a P - βa β b P = valR P.x (W a ⊓ W b) f := by
    intro a b
    obtain ⟨f, hf⟩ := GlobalTheory.T.exists_section_of_natural_on_algebraPoints_of_cover K A.left (A.hom ≫ 𝟙 (Sp K)) Unit (fun _ ↦ W a ⊓ W b) (W a ⊓ W b)
      (fun _ ↦ le_rfl) (le_iSup (fun _ : Unit ↦ W a ⊓ W b) ()) (fun P ↦ βa β a P - βa β b P) (fun _ P Q φ hP ↦ by
        change βa β a Q - βa β b Q = φ.ρ (βa β a P - βa β b P)
        rw [βa_step hβ a (hP.mono inf_le_left) φ, βa_step hβ b (hP.mono inf_le_right) φ, map_sub]
        ring)
    exact ⟨f, fun P hP ↦ hf () P hP⟩
  choose φab hφab using hsec
  have hcoc : ∀ (a b c : Idx U) (P : GPt A), P.In (W a) → P.In (W b) → P.In (W c) →
      valR P.x _ (φab a b) + valR P.x _ (φab b c) = valR P.x _ (φab a c) := by
    intro a b c P ha hb hc
    rw [← hφab a b P (ha.inf hb), ← hφab b c P (hb.inf hc), ← hφab a c P (ha.inf hc)]
    ring
  obtain ⟨ψ, hψn, hψ⟩ := GlobalTheory.T.derivative_cechCocycle_invariantVectorField_isCoboundary K A hA (Idx U) W (iSup_idx U hU) φab hcoc v hv
  let G : PtFn (A.hom ≫ 𝟙 (Sp K)) := fun P ↦
    if h : ∃ a, P.In (W a) then TrivSqZeroExt.snd (R := P.B) (βa β h.choose (P.tr v)) - ψ h.choose P else 0
  have hG : ∀ (a : Idx U) (P : GPt A), P.In (W a) →
      G P = TrivSqZeroExt.snd (R := P.B) (βa β a (P.tr v)) - ψ a P := by
    intro a P ha
    have h : ∃ a, P.In (W a) := ⟨a, ha⟩
    have hb : P.In (W h.choose) := h.choose_spec
    have e1 := hφab h.choose a (P.tr v) ((hb.inf ha).tr hv)
    have e2 := hψ h.choose a P hb ha
    change βa β h.choose (P.tr v) - βa β a (P.tr v) = valR (P.trx v) _ (φab h.choose a) at e1
    rw [← e1, TrivSqZeroExt.snd_sub] at e2
    simp only [G, dif_pos h]
    linear_combination e2
  refine ⟨G, fun i V hVU P Q φ hP ↦ ?_⟩
  let a : Idx U := ⟨(i, V), hVU⟩
  have hPa : P.In (W a) := hP
  have hQa : Q.In (W a) := hP.map φ
  rw [hG a P hPa, hG a Q hQa, hψn a P Q φ hPa]
  have e := βa_step hβ a (hPa.tr hv) (φ.tr v)
  have e' := congrArg (TrivSqZeroExt.snd (R := Q.B)) e
  change TrivSqZeroExt.snd (R := Q.B) (βa β a (Q.tr v)) =
    TrivSqZeroExt.snd (R := Q.B) (dualAlg φ.ρ (βa β a (P.tr v)) + β (P.tr v) (Q.tr v) (φ.tr v)) at e'
  rw [TrivSqZeroExt.snd_add, snd_dualAlg] at e'
  rw [map_sub]
  linear_combination -e'

end GlobalTheory.CocInv
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotFrames

open Formalism.L2.JoinChr




theorem chr_mem_of_idemSum {K : Type} [Field K] {σ : K →+* ℂ} {D : D7} {c : (AE D)ˣ →* Circle}
    {χ : Formalism.L2.Host.HChar D.host.E} (hc : ChrEq c χ) (hχ : LocIn σ χ) {e : AE D}
    {S : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e S) (x : (AE D)ˣ) (d : AE D)
    (hx : (x : AE D) = e * d + (1 - e)) : ((c x : Circle) : ℂ) ∈ σ.fieldRange := by
  classical
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2
    (GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3) c χ hc
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  have heT : ∀ P, ι (finPart D (∑ PP ∈ S, es PP)) P = if P ∈ S then 1 else 0 := by
    intro P

    rw [map_sum, map_sum, GlobalTheory.FlipCharFormula.fa_sum,
    Finset.sum_congr rfl (fun PP hPP => GlobalTheory.FlipCharFormula.comp_of_isIdemAt ι h1 h2 (hes PP hPP) P)]
    exact Finset.sum_ite_eq S P (fun _ => (1 : HeightOneSpectrum.adicCompletion D.host.E P))
  have hinfT : infPart D (∑ PP ∈ S, es PP) = 0 := by

    rw [map_sum]
    exact Finset.sum_eq_zero (fun PP hPP => GlobalTheory.FlipCharFormula.infPart_of_isIdemAt (hes PP hPP))
  have hinf : infPart D (x : AE D) = 1 := by
    rw [hx, map_add (f := _), map_mul, map_sub, hinfT, map_one, zero_mul, zero_add, sub_zero]
  have hout : ∀ P, P ∉ S → ι (finPart D (x : AE D)) P = 1 := by
    intro P hP
    rw [hx, map_add (f := _), map_mul, map_sub, map_one, map_add (f := _), map_mul, map_sub, map_one, GlobalTheory.FlipCharFormula.fa_add,
      GlobalTheory.FlipCharFormula.fa_mul, GlobalTheory.FlipCharFormula.fa_sub, GlobalTheory.FlipCharFormula.fa_one, heT, if_neg hP]
    simp
  have hne : ∀ P, ι (finPart D (x : AE D)) P ≠ 0 := by
    intro P h0
    have h := congrArg (fun z => ι (finPart D z) P) (Units.mul_inv x)
    simp only [map_mul, map_one, GlobalTheory.FlipCharFormula.fa_mul, GlobalTheory.FlipCharFormula.fa_one, h0, zero_mul] at h
    exact zero_ne_one h
  have hk : ∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ k : D.host.Eˣ,
      Valued.v (ι (finPart D (x : AE D)) P) = P.valuation D.host.E (k : D.host.E) ∧
      Valued.v (ι (finPart D (x : AE D)) P - algebraMap D.host.E _ (k : D.host.E)) ≤
        P.valuation D.host.E (N : D.host.E) * P.valuation D.host.E (k : D.host.E) := fun P => by
    obtain ⟨k, a, b, -⟩ := GlobalTheory.adicCompletion_exists_unit_approx D.host.E N hN P _ (hne P)
    exact ⟨k, a, b⟩
  choose k hk1 hk2 using hk
  have hI : Ideal.span {((N : ℕ) : 𝓞 D.host.E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN.ne'
  have key := hprod x hinf (S ∪ (Ideal.finite_factors hI).toFinset) k (fun P _ => ⟨hk1 P, hk2 P⟩)
    (fun P hP => by
      have hPS : P ∉ S := fun h => hP (Finset.mem_union_left _ h)
      refine ⟨by rw [hout P hPS, map_one], fun hNP => hP (Finset.mem_union_right _ ?_)⟩
      rw [Set.Finite.mem_toFinset]
      exact Ideal.dvd_span_singleton.mpr hNP)
  rw [key]
  refine Subfield.prod_mem _ fun P _ => ?_
  rw [← SetLike.mem_coe, RingHom.coe_fieldRange]
  exact hχ P _



theorem factor_mem_field : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (S : GridChoice W Set.univ)
    (μ₀ : T), L.Is μ₀ → NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (A A' WW : HSp D) (Y : Tri T A A' WW),
    IsBottomTri W i j Y → ∀ (t : T) (g : GA D A) (g' : GA D A') (h : GA D WW) (x x' y : (AE D)ˣ),
    Formalism.L2.Theta.SuppAt (Y.e t) A g → Formalism.IndefR.Lev.finE A g ∈ Formalism.L2.DIV.St Y.rA.β → Formalism.L2.Theta.IsDetAt (Y.e t) A g x →
    Formalism.L2.Theta.SuppAt (Y.e t) A' g' → Formalism.IndefR.Lev.finE A' g' ∈ Formalism.L2.DIV.St Y.rA'.β →
    Formalism.L2.Theta.IsDetAt (Y.e t) A' g' x' →
    Formalism.L2.Theta.SuppAt (Y.e t) WW h → Formalism.IndefR.Lev.finE WW h ∈ Formalism.L2.DIV.St Y.rW.β → Formalism.L2.Theta.IsDetAt (Y.e t) WW h y →
    ∃ z : D.what₂.LLˣ, D.what₂.embLL z =
      ((splitFacO (GlobalTheory.BotFrames.botAlpha L i j t) (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) x' y : Circle)
        : ℂ) /
      ((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t) x y : Circle) : ℂ) := by
  intro D T L sc G W S μ₀ hL hN i j A A' WW Y hY t g g' h x x' y _ _ hx _ _ hx' _ _ hy
  have he := hY.is.idem t
  have hm : 1 ≤ D.R.m - (i : ℕ) ∧ D.R.m - (i : ℕ) ≤ D.R.m := ⟨by omega, by omega⟩
  have mem : ∀ (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ → LocIn D.what₂.embLL χ →
      ∀ (u : (AE D)ˣ) (d : AE D), (u : AE D) = Y.e t * d + (1 - Y.e t) → ((c u : Circle) : ℂ) ∈ D.what₂.embLL.fieldRange :=
    fun c χ hc hχ u d hu => chr_mem_of_idemSum hc hχ he u d hu
  have m1 := mem _ _ (hL.mu0 j) (hN.chars.mu0 j)
  have m2 := mem _ _ (hL.xi t) (hN.chars.xi t)
  have m3 := mem _ _ (G.ch.chi_eq _ hm.1 hm.2) (hN.chars.chi _ hm.1 hm.2)
  set a := L.mu0 ((j : ℕ) + 1)
  set b := L.xi t
  set c := G.ch.chi (D.R.m - (i : ℕ))
  set η := L.eta ^ (rankV D i j % 2)
  have hv : ((splitFacO (GlobalTheory.BotFrames.botAlpha L i j t) (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) x' y : Circle)
        : ℂ) /
      ((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t) x y : Circle) : ℂ) =
      ((a x' : ℂ) * b x')⁻¹ * c x' * (((a x : ℂ) * b x)⁻¹ * c x) * ((a y : ℂ) * b y * (c y : ℂ)⁻¹) := by
    have e1 : GlobalTheory.BotFrames.botAlpha L i j t = a * b * η := rfl
    have e2 : GlobalTheory.BotFrames.botBeta G i j = c * η := rfl
    rw [e1, e2]
    simp only [splitFacO, MonoidHom.div_apply, MonoidHom.mul_apply, Circle.coe_mul, Circle.coe_inv, Circle.coe_div]
    have n1 := Circle.coe_ne_zero (a x'); have n2 := Circle.coe_ne_zero (b x'); have n3 := Circle.coe_ne_zero (c x')
    have n4 := Circle.coe_ne_zero (η x'); have n5 := Circle.coe_ne_zero (a x); have n6 := Circle.coe_ne_zero (b x)
    have n7 := Circle.coe_ne_zero (c x); have n8 := Circle.coe_ne_zero (η x); have n9 := Circle.coe_ne_zero (a y)
    have n10 := Circle.coe_ne_zero (b y); have n11 := Circle.coe_ne_zero (c y); have n12 := Circle.coe_ne_zero (η y)
    field_simp
  have hmem : (((splitFacO (GlobalTheory.BotFrames.botAlpha L i j t) (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) x' y : Circle)
        : ℂ) /
      ((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t) x y : Circle) : ℂ)) ∈
      D.what₂.embLL.fieldRange := by
    rw [hv]
    refine mul_mem (mul_mem (mul_mem (inv_mem (mul_mem (m1 _ _ hx') (m2 _ _ hx'))) (m3 _ _ hx'))
      (mul_mem (inv_mem (mul_mem (m1 _ _ hx) (m2 _ _ hx))) (m3 _ _ hx)))
      (mul_mem (mul_mem (m1 _ _ hy) (m2 _ _ hy)) (inv_mem (m3 _ _ hy)))
  obtain ⟨z, hz⟩ := hmem
  have hne : ((splitFacO (GlobalTheory.BotFrames.botAlpha L i j t) (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) x' y : Circle)
        : ℂ) /
      ((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t) x y : Circle) : ℂ) ≠ 0 :=
    div_ne_zero (Circle.coe_ne_zero _) (Circle.coe_ne_zero _)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [map_zero] at hz
    exact hne hz.symm
  exact ⟨Units.mk0 z hz0, hz⟩

end GlobalTheory.BotFrames

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotMove

noncomputable section

open MeasureTheory GlobalTheory.Grid

namespace GlobalTheory.BotMove

variable {D : D7} {T : Type} {A A' WW : HSp D}

theorem moveTri_ker (Y : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    {α β : T → ((AE D)ˣ →* Circle)} {νH : T → HChar D.host.E} {S : T → Finset (Formalism.L2.DIV.Pl D.host.E)}
    (hY : Y.Is ψ θ α β νH S) (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E))
    (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E))
    {g : GA D A} (hg : g ∈ GfC A) (g' : GA D A') {h : GA D WW} (hh : h ∈ GfC WW) (t₀ : T) (r r' : T → ℂ)
    (t : T) (P : PolF D WW.rank A.rank) (y : GA D WW) (x : GA D A) :
    (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ker ψ θ t P y x = (r t)⁻¹ * Y.ker ψ θ t P (y * h) (x * g) := by
  have hgs : (ofSgn true A).symm g ∈ GfC (neg A) := hg
  have key : Y.ω t (g, h) (pureTensorO ψ θ (neg A) WW (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.B Y.rW.B (Y.f t) P) =
      pureTensorO ψ θ (neg A) WW (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.B Y.rW.B (Y.ω t (g, h) (Y.f t)) P :=
    (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ (neg A) WW _ _ ((Y.ω t).toSgn true) (hY.weil t) hY.isVac.2.inf
      (fun τ => -Y.rA.s τ) (fun τ => -Y.rA.s τ) Y.rA.B Y.rA.B Y.rW.s Y.rW.s Y.rW.B Y.rW.B ((ofSgn true A).symm g) h
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hgs, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hh, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hgs, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hh, Matrix.one_mul])
      (Y.f t) (GlobalTheory.ConstRatio.theta_f hY t).1 P).2
  show Y.ω t (x, y) (pureTensorO ψ θ (neg A) WW (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.B Y.rW.B
      ((r t)⁻¹ • Y.ω t (g, h) (Y.f t)) P) 0 =
    (r t)⁻¹ * Y.ω t (x * g, y * h) (pureTensorO ψ θ (neg A) WW (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.B Y.rW.B (Y.f t) P) 0
  rw [GlobalTheory.FiniteFock.pureTensorO_smul, map_smul, Pi.smul_apply, smul_eq_mul, ← key, ← Module.End.mul_apply, ← map_mul]
  rfl

theorem moveTri_I : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (Y : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → HChar D.host.E) (S : T → Finset (Formalism.L2.DIV.Pl D.host.E)),
    Y.Is ψ θ α β νH S →
    ∀ (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E))
      (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)),
    ∀ g ∈ GfC A, ∀ (g' : GA D A'), ∀ h ∈ GfC WW, ∀ (t₀ : T) (r r' : T → ℂ), (∀ t, r t ≠ 0) →
    ∀ t P (y : GA D WW),
      (MeasureTheory.IntegrableOn ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ker ψ θ t P y) (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').fd
          (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').m ↔ MeasureTheory.IntegrableOn (Y.ker ψ θ t P (y * h)) Y.fd Y.m) ∧
      (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').I ψ θ t P y = (r t)⁻¹ * Y.I ψ θ t P (y * h) := by
  intro D T A A' WW Y ψ θ α β νH S hY ΛA ΛA' ΛW g hg g' h hh t₀ r r' hr t P y
  have hk : (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ker ψ θ t P y = fun x => (r t)⁻¹ * Y.ker ψ θ t P (y * h) (x * g) :=
    funext (moveTri_ker Y ψ θ hY ΛA ΛA' ΛW hg g' hh t₀ r r' t P y)
  have he : MeasurableEmbedding (fun x : GA D A => x * g⁻¹) := (MeasurableEquiv.mulRight g⁻¹).measurableEmbedding
  have hpre : (fun x : GA D A => x * g⁻¹) ⁻¹' ((fun x => x * g) ⁻¹' Y.fd) = Y.fd := by
    ext x; simp
  have hu : IsUnit (r t)⁻¹ := isUnit_iff_ne_zero.2 (inv_ne_zero (hr t))
  constructor
  · show IntegrableOn ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ker ψ θ t P y) ((fun x => x * g) ⁻¹' Y.fd)
      (Y.m.map fun x => x * g⁻¹) ↔ _
    rw [he.integrableOn_map_iff, hpre, hk]
    simp only [Function.comp_def, inv_mul_cancel_right]
    exact integrable_const_mul_iff hu _
  · show ∫ x in (fun x => x * g) ⁻¹' Y.fd, (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ker ψ θ t P y x ∂(Y.m.map fun x => x * g⁻¹) =
      (r t)⁻¹ * ∫ x in Y.fd, Y.ker ψ θ t P (y * h) x ∂Y.m
    rw [he.setIntegral_map, hpre, hk]
    simp only [inv_mul_cancel_right]
    exact integral_const_mul _ _

end GlobalTheory.BotMove

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotMove

namespace GlobalTheory.BotMove

open MeasureTheory

theorem int_prime_moveTri : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (Y : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → HChar D.host.E) (S : T → Finset (Formalism.L2.DIV.Pl D.host.E)),
    Y.Is ψ θ α β νH S →
    ∀ (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E))
      (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)),
    ∀ (g : GA D A), ∀ g' ∈ GfC A', ∀ h ∈ GfC WW, ∀ (t₀ : T) (r r' : T → ℂ), (∀ t, r' t ≠ 0) →
    ∀ t P (y : GA D WW),
      (MeasureTheory.IntegrableOn ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ker' ψ θ t P y) (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').fd'
          (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').m' ↔ MeasureTheory.IntegrableOn (Y.ker' ψ θ t P (y * h)) Y.fd' Y.m') ∧
      (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').I' ψ θ t P y = (r' t)⁻¹ * Y.I' ψ θ t P (y * h) := by
  intro D T A A' WW Y ψ θ α β νH S hY ΛA ΛA' ΛW g g' hg' h hh t₀ r r' hr' t P y
  have hW : IsWeilDatumO ψ A' WW (α t) (α t / β t) (Y.ω' t) := hY.weil' t
  have hθ : IsInfFam θ := hY.isVac'.2.inf
  have hf := (GlobalTheory.ConstRatio.theta_f hY t).2
  have hk : ∀ x, (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ker' ψ θ t P y x = (r' t)⁻¹ * Y.ker' ψ θ t P (y * h) (x * g') := by
    intro x
    change thetaKO (Y.ω' t) x y (pureTensorO ψ θ A' WW Y.rA'.s Y.rW.s Y.rA'.B Y.rW.B
      ((r' t)⁻¹ • Y.ω' t (g', h) (Y.f' t)) P) = (r' t)⁻¹ * thetaKO (Y.ω' t) (x * g') (y * h)
        (pureTensorO ψ θ A' WW Y.rA'.s Y.rW.s Y.rA'.B Y.rW.B (Y.f' t) P)
    rw [GlobalTheory.FiniteFock.pureTensorO_smul, ← (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ A' WW _ _ (Y.ω' t) hW hθ
      Y.rA'.s Y.rA'.s Y.rA'.B Y.rA'.B Y.rW.s Y.rW.s Y.rW.B Y.rW.B g' h
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hg', Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hh, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hg', Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hh, Matrix.one_mul]) _ hf P).2]
    simp only [thetaKO, map_smul, Pi.smul_apply, smul_eq_mul]
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk]
  let e : GA D A' ≃ᵐ GA D A' := MeasurableEquiv.mulRight g'⁻¹
  have hm : (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').m' = Y.m'.map e := rfl
  have hs : e ⁻¹' (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').fd' = Y.fd' := by
    ext x
    change x * g'⁻¹ * g' ∈ Y.fd' ↔ x ∈ Y.fd'
    rw [inv_mul_cancel_right]
  have hc : ∀ x, (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ker' ψ θ t P y (e x) = (r' t)⁻¹ * Y.ker' ψ θ t P (y * h) x := by
    intro x
    rw [hk]
    change (r' t)⁻¹ * Y.ker' ψ θ t P (y * h) (x * g'⁻¹ * g') = _
    rw [inv_mul_cancel_right]
  have hu : IsUnit (r' t)⁻¹ := IsUnit.mk0 _ (inv_ne_zero (hr' t))
  constructor
  · rw [hm, integrableOn_map_equiv, hs]
    change Integrable (fun x => (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ker' ψ θ t P y (e x)) (Y.m'.restrict Y.fd') ↔ _
    simp_rw [hc]
    exact integrable_const_mul_iff hu _
  · change ∫ x in (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').fd', (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ker' ψ θ t P y x
        ∂(moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').m' = (r' t)⁻¹ * ∫ x in Y.fd', Y.ker' ψ θ t P (y * h) x ∂Y.m'
    rw [hm, setIntegral_map_equiv, hs]
    simp_rw [hc]
    exact integral_const_mul _ _

end GlobalTheory.BotMove
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.doubledWeil_inert_place_vacuum_eigenfunction : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T → ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')))
      (omd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) →* Module.End ℂ ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → AF F) → ℂ)),
      IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) G.M'.co dd →
      IsUWeilSplit (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) dd X.α (diagCols (Fin (a + a'))) omd →
    ∀ R : (Fin a' × Fin (a + a') → AF F) → ℂ, R 0 ≠ 0 → Rest (evFin F v) (G.M'.vac v) R →
    ∀ g ∈ GlobalTheory.InertDbl.KAtD σ G.W v, ∃ c : ℂ, omd g (GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R)) =
      c • GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) := by
  first | exact @GlobalTheory.DblVacLine.dblFun_eigen | exact GlobalTheory.DblVacLine.dblFun_eigen | (intros; apply GlobalTheory.DblVacLine.dblFun_eigen <;> assumption)
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.lieScalar_of_prints_derEx_vacLine : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.VacLine → GlobalTheory.RealLift.LieScalar := by
  first | exact @GlobalTheory.LieScal.lieScalar | exact GlobalTheory.LieScal.lieScalar | (intros; apply GlobalTheory.LieScal.lieScalar <;> assumption)
end
