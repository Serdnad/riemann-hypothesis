module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1968
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1770
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2174
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle058
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameBorelGroupoidProperties
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle026
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle044
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne

@[expose] public section

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Classical

noncomputable section
namespace GlobalTheory.VacFactor

theorem pure_update_smul {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f : SInf F κ)
    (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) (w : Pl (F := F)) (r : ℂ) (h : (κ → Fv F w) → ℂ)
    (hφ : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers F} 1) :
    pure f (Function.update φ w (r • h)) = pure (r • f) (Function.update φ w h) := by
  funext x
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
  rw [GlobalTheory.PureFactor.finprod_update φ w (r • h) hφ x, GlobalTheory.PureFactor.finprod_update φ w h hφ x]
  simp only [SchwartzMap.smul_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem tens_smul {F : Type} [Field F] [NumberField F] {R κ : Type} (ev : AF F → R) (c : ℂ) (g : (κ → R) → ℂ)
    (r : (κ → AF F) → ℂ) : tens ev (c • g) r = c • tens ev g r := by
  funext x
  simp [tens, mul_assoc]

theorem std_of_off {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (vac φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ)
    (hvac : ∀ᶠ v in Filter.cofinite, vac v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers F} 1)
    (U : Finset (Pl (F := F))) (h : ∀ v, v ∉ U → φ v = vac v) :
    ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers F} 1 := by
  filter_upwards [hvac, U.finite_toSet.compl_mem_cofinite] with v h1 h2
  rw [h v h2, h1]

theorem factor : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (S : Finset (Pl (F := F))) (f : SInf F (Fin a' × Fin (a + a'))) (φ : ∀ w : Pl (F := F), (Fin a' × Fin (a + a') → Fv F w) → ℂ),
    (∀ w, φ w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) → (∀ w, w ∉ S → φ w = G.M'.vac w) →
    ∀ Ψ ∈ schA F (Fin a' × Fin (a + a')),
    (∀ w, w ∉ S → ∀ γ ∈ latAtV G.V' G.W w, ∀ c : ℂ,
      G.M'.co.rho B.ψ γ (pure f φ) = c • pure f φ → G.M'.co.rho B.ψ γ Ψ = c • Ψ) →
    ∃ (m : ℕ) (f' : Fin m → SInf F (Fin a' × Fin (a + a'))) (φ' : Fin m → ∀ w : Pl (F := F), (Fin a' × Fin (a + a') → Fv F w) → ℂ),
      (∀ i w, φ' i w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) ∧ (∀ i w, w ∉ S → φ' i w = G.M'.vac w) ∧
      Ψ = ∑ i, pure (f' i) (φ' i) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT S f φ hφSB hφvac Ψ hΨ hyp
  have hvstd := hT.geo.hM'.std
  have hvSB : ∀ v, G.M'.vac v ∈ SB (Fin a' × Fin (a + a') → Fv F v) := fun v => (hT.geo.hM'.vac v).1
  have hyp' : ∀ w, w ∉ S → ∀ γ ∈ latAtV G.V' G.W w, ∀ c : ℂ,
      Acts (evFin F w) (G.M'.co.rho B.ψ γ) (G.M'.vac w) (c • G.M'.vac w) → G.M'.co.rho B.ψ γ Ψ = c • Ψ := by
    intro w hw γ hγ c hc
    have hstd := std_of_off G.M'.vac φ hvstd S hφvac
    obtain ⟨r, hr1, hr2⟩ := GlobalTheory.PureFactor.exists_rest_factor w f φ hstd
    have e : pure f φ = tens (evFin F w) (G.M'.vac w) r := by
      rw [hr2, ← hφvac w hw, Function.update_eq_self]
    refine hyp w hw γ hγ c ?_
    have hR : Rest (evFin F w) (G.M'.vac w) r := ⟨hr1, e ▸ GlobalTheory.TensUniq.pure_mem_schA f φ hφSB hstd⟩
    rw [e, hc r hR, tens_smul]
  obtain ⟨T, m, f₀, φ₀, hSB₀, hstd₀, hsum₀⟩ := GlobalTheory.T.adelic_schwartz_finite_pure_tensors F _ Ψ hΨ
  have hfin : {v | ¬ G.M'.vac v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers F} 1}.Finite :=
    Filter.eventually_cofinite.1 hvstd
  have key : ∀ U : Finset (Pl (F := F)), ∀ (f : Fin m → SInf F (Fin a' × Fin (a + a')))
      (φ : Fin m → ∀ v : Pl (F := F), (Fin a' × Fin (a + a') → Fv F v) → ℂ),
      (∀ i v, φ i v ∈ SB (Fin a' × Fin (a + a') → Fv F v)) → (∀ i v, v ∉ S → v ∉ U → φ i v = G.M'.vac v) →
      Ψ = ∑ i, pure (f i) (φ i) →
      ∃ (f' : Fin m → SInf F (Fin a' × Fin (a + a'))) (φ' : Fin m → ∀ v : Pl (F := F), (Fin a' × Fin (a + a') → Fv F v) → ℂ),
        (∀ i v, φ' i v ∈ SB (Fin a' × Fin (a + a') → Fv F v)) ∧ (∀ i v, v ∉ S → φ' i v = G.M'.vac v) ∧
        Ψ = ∑ i, pure (f' i) (φ' i) := by
    intro U
    induction U using Finset.induction_on with
    | empty => exact fun f φ h1 h2 h3 => ⟨f, φ, h1, fun i v hv => h2 i v hv (Finset.notMem_empty v), h3⟩
    | insert w U hwU ih =>
      intro f φ h1 h2 h3
      by_cases hwS : w ∈ S
      · refine ih f φ h1 (fun i v hv hvU => h2 i v hv ?_) h3
        rw [Finset.mem_insert]
        rintro (rfl | h)
        exacts [hv hwS, hvU h]
      · have hstd : ∀ i, ∀ᶠ v in Filter.cofinite,
            φ i v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers F} 1 := fun i =>
          std_of_off G.M'.vac (φ i) hvstd (S ∪ insert w U) fun v hv =>
            h2 i v (fun h => hv (Finset.mem_union_left _ h)) (fun h => hv (Finset.mem_union_right _ h))
        obtain ⟨g, hgSB, hgE, hgsum⟩ := GlobalTheory.T.triple_lattice_invariant_schwartz_global hP F E σ B a a' G X om om' hT w Ψ hΨ (hyp' w hwS) m f φ h1 hstd h3
        choose r hr using fun i => GlobalTheory.T.triple_lattice_invariant_schwartz_local hP F E σ B a a' G X om om' hT w (g i) (hgSB i) (hgE i)
        refine ih (fun i => r i • f i) (fun i => Function.update (φ i) w (G.M'.vac w)) (fun i v => ?_)
          (fun i v hv hvU => ?_) ?_
        · by_cases hvw : v = w
          · subst hvw
            rw [Function.update_self]
            exact hvSB _
          · rw [Function.update_of_ne hvw]
            exact h1 i v
        · by_cases hvw : v = w
          · subst hvw
            rw [Function.update_self]
          · rw [Function.update_of_ne hvw]
            refine h2 i v hv ?_
            rw [Finset.mem_insert]
            rintro (h | h)
            exacts [hvw h, hvU h]
        · rw [hgsum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hr i, pure_update_smul _ _ _ _ _ (hstd i)]
  obtain ⟨f', φ', h1, h2, h3⟩ := key (T ∪ hfin.toFinset) f₀ φ₀ hSB₀ (fun i v _ hv => by
    rw [hstd₀ i v (fun h => hv (Finset.mem_union_left _ h))]
    by_contra hne
    exact hv (Finset.mem_union_right _ (hfin.mem_toFinset.2 fun h => hne h.symm))) hsum₀
  exact ⟨m, f', φ', h1, h2, h3⟩

end GlobalTheory.VacFactor
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.CompHS GlobalTheory.CxPts GlobalTheory.Vanishing
open GlobalTheory.TangentOrigin GlobalTheory.CechPic GlobalTheory.TopForm GlobalTheory.Adelic

namespace GlobalTheory.CompHS

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y}
  {Z : Comp Xo c}

theorem evalPt_appLE_of_comp {R : Type} [CommRing R] {A B : Scheme.{0}} (v : Sp R ⟶ A) (φ : A ⟶ B) (U : B.Opens)
    (V : A.Opens) (e : V ≤ φ ⁻¹ᵁ U) (f : Γ(B, U)) (hV : ⊤ ≤ v ⁻¹ᵁ V) (hU : ⊤ ≤ (v ≫ φ) ⁻¹ᵁ U) :
    evalPt v V hV (φ.appLE U V e f) = evalPt (v ≫ φ) U hU f := by
  simp only [evalPt, CommRingCat.hom_comp, RingHom.comp_apply]
  rw [← CommRingCat.comp_apply (φ.appLE U V e), Scheme.Hom.appLE_comp_appLE]

theorem canId_val_mul_det (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) (ω : CanId M)
    {L : Type} [Field L] [iL : Algebra c.F L] (Q : FrPt Xo c L)
    (v : GlobalTheory.FlagTan.TIx Dw (GlobalTheory.FlagTan.psiSet H) → FrPt Xo c (DualNumber L))
    (hv : GlobalTheory.FlagTan.IsTanFrame (GlobalTheory.FlagTan.psiSet H) Q v) (z : Sp L ⟶ M.X)
    (zv : GlobalTheory.FlagTan.TIx Dw (GlobalTheory.FlagTan.psiSet H) → (Sp (DualNumber L) ⟶ M.X)) (i : M.K.bundle.ι) (k : X.F.J)
    (O : M.X.Opens) (hO : O ≤ M.K.bundle.U i) (g : Fin (GlobalTheory.FlagTan.dimFlag Dw) → Γ(M.X, O)) (hz : ⊤ ≤ z ⁻¹ᵁ O)
    (hzv : ∀ b, ⊤ ≤ zv b ⁻¹ᵁ O) (hk : ⊤ ≤ (z ≫ toFlag M) ⁻¹ᵁ X.F.U k) (ho : ⊤ ≤ z ⁻¹ᵁ M.off)
    (hi : ⊤ ≤ z ⁻¹ᵁ (LB.div M.K.bundle ((L₀ X Z (GlobalTheory.FlagTan.kap Dw)).pull M.σ)).U (i, flagIdx M _ k))
    (hQ : X.F.ChartFr k (z ≫ toFlag M) hk Q) (hl : ∀ b, zv b ≫ toFlag M = X.ptY (v b)) :
    H0.val (B := LB.div M.K.bundle ((L₀ X Z (GlobalTheory.FlagTan.kap Dw)).pull M.σ)) z (i, flagIdx M _ k) ho hi ω.ω *
        (Matrix.of fun a b => (evalPt (zv (tanOrd Dw b)) O (hzv _) (g a)).snd).det =
      evalPt z O hz (M.K.jacobian i hO g) := by
  have hb := (GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c L).1 Q
  have a := ω.isKS L Q Q 1 v z zv i k O hO g hz hzv hk ho hi hQ hb hv hl
  simpa only [Pi.one_apply, one_zpow, Finset.prod_const_one, Units.val_one, one_mul] using a

end GlobalTheory.CompHS
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS


open TrivSqZeroExt in
theorem exists_spMap_fst_eq {S : Type} [CommRing S] (s : Sp (DualNumber S)) :
    ∃ t : Sp S, spMap (fstHom S S S).toRingHom t = s := by
  refine ⟨PrimeSpectrum.comap (inlHom S S) s, ?_⟩
  show PrimeSpectrum.comap _ (PrimeSpectrum.comap _ s) = s
  ext x
  have hr : inr x.snd ∈ s.asIdeal := s.2.mem_of_pow_mem 2 (by
    rw [show (inr x.snd : DualNumber S) ^ 2 = 0 by ext <;> simp [pow_two]]
    exact s.asIdeal.zero_mem)
  simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
  change inl x.fst ∈ s.asIdeal ↔ x ∈ s.asIdeal
  have e1 : inl x.fst + inr x.snd = x := inl_fst_add_inr_snd_eq x
  have e2 : inl x.fst = x - inr x.snd := eq_sub_of_add_eq e1
  constructor
  · intro h
    rw [← e1]
    exact s.asIdeal.add_mem h hr
  · intro h
    rw [e2]
    exact s.asIdeal.sub_mem h hr

theorem le_preimage_of_fst {S : Type} [CommRing S] {T : Scheme.{0}} (x : Sp (DualNumber S) ⟶ T) (V : T.Opens)
    (h : ⊤ ≤ (spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ x) ⁻¹ᵁ V) : ⊤ ≤ x ⁻¹ᵁ V := by
  intro s _
  obtain ⟨t, rfl⟩ := exists_spMap_fst_eq s
  exact h (Set.mem_univ t)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c}
  (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw))

theorem exists_dualLift {S : Type} [CommRing S] [Algebra c.F S] {Q : FrPt Xo c S} {v : FrPt Xo c (DualNumber S)}
    (hv : FrMap (TrivSqZeroExt.fstHom c.F S S) v Q) {z : Sp S ⟶ M.X} (hz : z ≫ toFlag M = X.ptY Q)
    (ho : ⊤ ≤ z ⁻¹ᵁ M.off) :
    ∃ zv : Sp (DualNumber S) ⟶ M.X, zv ≫ toFlag M = X.ptY v ∧
      spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ zv = z := by
  have e : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ X.ptY v = z ≫ toFlag M :=
    (X.ptY_frMap hv).trans hz.symm
  have hU : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ U₀ X Z := fun s _ => by
    have := ho (Set.mem_univ s)
    rw [M.off_eq] at this
    exact this
  have hb : ⊤ ≤ X.ptY v ⁻¹ᵁ (inc₀ X Z).opensRange := le_preimage_of_fst _ _ (by
    rw [e]
    rintro s -
    exact ⟨(z ≫ M.σ) s, rfl⟩)
  have hr : Set.range (X.ptY v) ⊆ Set.range (inc₀ X Z) := by
    rintro _ ⟨s, rfl⟩
    exact hb (Set.mem_univ s)
  obtain ⟨w, hw⟩ : ∃ w, w ≫ inc₀ X Z = X.ptY v := ⟨_, IsOpenImmersion.lift_fac _ _ hr⟩
  have ered : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ w = z ≫ M.σ := by
    rw [← cancel_mono (inc₀ X Z), Category.assoc, hw, e, Category.assoc]
  have hwU : ⊤ ≤ w ⁻¹ᵁ U₀ X Z := le_preimage_of_fst _ _ (by rw [ered]; exact hU)
  obtain ⟨zv, hzv, -⟩ := M.existsUnique_lift w hwU
  have hred : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ zv = z :=
    (M.existsUnique_lift (z ≫ M.σ) hU).unique (by rw [Category.assoc, hzv, ered]) rfl
  refine ⟨zv, ?_, hred⟩
  rw [toFlag, ← Category.assoc, hzv, hw]

def vertMat {S : Type} [CommRing S] (b : VIx Dw) (σ : E →+* ℂ) :
    Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) (DualNumber S) :=
  Matrix.of fun i j => TrivSqZeroExt.inl ((1 : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S) i j) +
    TrivSqZeroExt.inr ((Pi.single b.toF (1 : S) : GlobalTheory.FlagTan.FIx Dw → S) (some ⟨σ, i, j⟩))

theorem isUnit_det_vertMat {S : Type} [CommRing S] (b : VIx Dw) (σ : E →+* ℂ) :
    IsUnit (vertMat (S := S) b σ).det := by
  have e : (TrivSqZeroExt.fstHom S S S).toRingHom.mapMatrix (vertMat (S := S) b σ) = 1 := by
    ext i j; simp [vertMat]
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
  show IsUnit ((TrivSqZeroExt.fstHom S S S).toRingHom _)
  rw [RingHom.map_det, e, Matrix.det_one]
  exact isUnit_one

theorem exists_vertLift (k : X.F.J) (W : M.X.Opens) (hW : IsAffineOpen W)
    (hle : W ≤ M.off ⊓ (toFlag M) ⁻¹ᵁ X.F.U k) :
    ∃ e : VIx Dw → (Γ(M.X, W) →+* DualNumber Γ(M.X, W)), (∀ b s, (e b s).fst = s) ∧
      ∀ (K : Type) [Field K] [Algebra c.F K] (ψ : Γ(M.X, W) →+* K)
        (hk : ⊤ ≤ ((spMap ψ ≫ tau hW) ≫ toFlag M) ⁻¹ᵁ X.F.U k) (Q : FrPt Xo c K),
        X.F.ChartFr k _ hk Q → ∀ b : VIx Dw, ∃ w : FrPt Xo c (DualNumber K),
          IsVert Q (Pi.single b.toF (1 : K)) w ∧
          spMap ((dualMap ψ).comp (e b)) ≫ tau hW ≫ toFlag M = X.ptY w := by
  have hτo : ⊤ ≤ tau hW ⁻¹ᵁ M.off := tau_le hW (hle.trans inf_le_left)
  have hτk : ⊤ ≤ (tau hW ≫ toFlag M) ⁻¹ᵁ X.F.U k := fun x hx => tau_le hW (hle.trans inf_le_right) hx
  have hF : ⊤ ≤ (tau hW ≫ toFlag M) ⁻¹ᵁ flagOpen X := fun x hx => by
    have := hτo hx
    rw [M.off_eq] at this
    exact this
  obtain ⟨_, hch⟩ := exists_chartFr _ hF
  obtain ⟨Q₀, hQ₀⟩ := hch k hτk
  have e₀ : tau hW ≫ toFlag M = X.ptY Q₀ := GlobalTheory.FlagMod.FlagCover.eq_ptY hQ₀.lies
  obtain ⟨Q₁, hQ₁⟩ := GlobalTheory.FlagTan.exists_frMap (TrivSqZeroExt.inlAlgHom c.F Γ(M.X, W) Γ(M.X, W)) Q₀
  have hred : FrMap (TrivSqZeroExt.fstHom c.F Γ(M.X, W) Γ(M.X, W)) Q₁ Q₀ :=
    GlobalTheory.FlagTan.frMap_of_comp hQ₁ (GlobalTheory.FlagTan.frMap_id Q₀) fun _ => rfl
  have hV : ∀ b : VIx Dw, ∃ V : FrPt Xo c (DualNumber Γ(M.X, W)),
      GlobalTheory.Frames.FrChg (vertMat b) ((1 : (DualNumber Γ(M.X, W))ˣ) : DualNumber Γ(M.X, W)) Q₁ V := fun b =>
    (GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c _ Q₁ (vertMat b) 1 (isUnit_det_vertMat b)).exists
  choose V hV using hV
  have hVr : ∀ b, FrMap (TrivSqZeroExt.fstHom c.F Γ(M.X, W) Γ(M.X, W)) (V b) Q₀ := fun b => by
    refine (GlobalTheory.FlagTan.frMap_iff_frChg (hV b) hred).2 ?_
    convert (GlobalTheory.Frames.frChg_calculus E H Dw l Xo c Γ(M.X, W)).2.1 Q₀ using 2 with σ
    · ext i j; simp [vertMat]
    · simp
  choose zv hzv hzr using fun b => exists_dualLift M (hVr b) e₀ hτo
  have hzW : ∀ b, ⊤ ≤ zv b ⁻¹ᵁ W := fun b => le_preimage_of_fst _ _ (by rw [hzr b]; exact tau_le hW le_rfl)
  refine ⟨fun b => GlobalTheory.FlagMod.ev (zv b) W (hzW b), fun b s => ?_, ?_⟩
  · have h' : ⊤ ≤ (spMap (TrivSqZeroExt.fstHom Γ(M.X, W) Γ(M.X, W) Γ(M.X, W)).toRingHom ≫ zv b) ⁻¹ᵁ W := by
      rw [hzr b]; exact tau_le hW le_rfl
    have h1 := GlobalTheory.FlagMod.ev_spMap _ (zv b) W (hzW b) h'
    rw [GlobalTheory.FlagMod.ev_congr (hzr b) W h' (tau_le hW le_rfl), GlobalTheory.FlagMod.ev_tau_self] at h1
    exact (DFunLike.congr_fun h1 s).symm
  intro K _ _ ψ hk Q hQ b

  have hx : frX Q = spMap ψ ≫ frX Q₀ := by
    let w₀ : Sp Γ(M.X, W) ⟶ X.Yo := pullback.lift (tau hW ≫ toFlag M) (frX Q₀) hQ₀.over.symm
    let w₁ : Sp K ⟶ X.Yo := pullback.lift ((spMap ψ ≫ tau hW) ≫ toFlag M) (frX Q) hQ.over.symm
    have e : w₁ = spMap ψ ≫ w₀ := by
      rw [← cancel_mono X.inc]
      simp only [w₀, w₁, Category.assoc, pullback.lift_fst]
    have := congrArg (· ≫ pullback.snd X.π Y.j) e
    simpa only [w₀, w₁, Category.assoc, pullback.lift_snd] using this
  have hs : spMap (algebraMap c.F K) = spMap (ψ.comp (algebraMap c.F Γ(M.X, W))) := by
    rw [← frX_snd Q, hx, Category.assoc, frX_snd Q₀, spMap_comp']
  have hψ : ψ.comp (algebraMap c.F Γ(M.X, W)) = algebraMap c.F K :=
    (congrArg CommRingCat.Hom.hom (Spec.map_injective hs)).symm
  let φ : Γ(M.X, W) →ₐ[c.F] K := { ψ with commutes' := fun r => DFunLike.congr_fun hψ r }
  let φε : DualNumber Γ(M.X, W) →ₐ[c.F] DualNumber K :=
    { dualMap ψ with
      commutes' := fun r => by
        ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl', ← DFunLike.congr_fun hψ r] }
  obtain ⟨Q', hQ'⟩ := GlobalTheory.FlagTan.exists_frMap φ Q₀
  have eQ : Q = Q' := hQ.unique (hQ₀.frMap hQ' (by rw [Category.assoc]) hk)
  subst eQ
  obtain ⟨y₀, hy₀⟩ := GlobalTheory.FlagTan.exists_frMap φε Q₁
  obtain ⟨w, hw⟩ := GlobalTheory.FlagTan.exists_frMap φε (V b)
  refine ⟨w, ⟨y₀, GlobalTheory.FlagTan.frMap_of_comp hQ' (GlobalTheory.FlagTan.frMap_comp (χ := φε.comp (TrivSqZeroExt.inlAlgHom c.F Γ(M.X, W) Γ(M.X, W))) hQ₁ hy₀ fun _ => rfl) fun a => ?_, ?_⟩, ?_⟩
  · ext <;> simp [φ, φε, dualMap]
  · have h2 := (GlobalTheory.FlagTan.frMap_iff_frChg (hV b) hy₀).1 hw
    unfold GlobalTheory.FlagTan.IsShift
    convert h2 using 2 with σ
    · ext i j <;> simp [GlobalTheory.FlagTan.unip, vertMat, φε, dualMap, Matrix.one_apply, Pi.single_apply] <;> split_ifs <;> simp
    · ext <;> simp [GlobalTheory.FlagTan.unip₀, φε, dualMap, GlobalTheory.FlagTan.VIx.toF]
  · have h3 : spMap (GlobalTheory.FlagMod.ev (zv b) W (hzW b)) ≫ tau hW = zv b := GlobalTheory.FlagMod.spMap_ev (zv b) hW (hzW b)
    rw [← spMap_comp', Category.assoc, ← Category.assoc (spMap _) (tau hW), h3, hzv b]
    have e4 : dualMap ψ = φε.toRingHom := RingHom.ext fun _ => rfl
    rw [e4]
    exact X.ptY_frMap hw

end GlobalTheory.CompHS
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open IsDedekindDomain

noncomputable section

namespace GlobalTheory.AfUnit

variable {p : ℕ} [Fact p.Prime]

theorem exists_nat_mem (v : AwayP p) : ∃ l : ℕ, 0 < l ∧ l.Coprime p ∧ (l : ℤ) ∈ v.1.asIdeal := by
  have hp : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 Fact.out
  have hmax : v.1.asIdeal.IsMaximal := v.1.isMaximal
  have hmp : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).2 hp
  have hnle : ¬ v.1.asIdeal ≤ Ideal.span {(p : ℤ)} := fun hle => v.2 (hmax.eq_of_le hmp.ne_top hle)
  obtain ⟨x, hx, hxp⟩ := Set.not_subset.1 hnle
  have hxp' : ¬ (p : ℤ) ∣ x := fun hd => hxp (Ideal.mem_span_singleton.2 hd)
  refine ⟨x.natAbs, Int.natAbs_pos.2 (fun h0 => hxp' (h0 ▸ dvd_zero _)), ?_, ?_⟩
  · exact ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 (fun hd => hxp' (Int.natCast_dvd.2 hd))).symm
  · rcases Int.natAbs_eq x with h1 | h1
    · rw [← h1]; exact hx
    · rw [← neg_eq_iff_eq_neg.2 h1]; exact neg_mem hx

theorem val_natCast (v : AwayP p) (m : ℕ) :
    Valued.v ((m : ℕ) : v.1.adicCompletion ℚ) = v.1.valuation ℚ (algebraMap ℤ ℚ (m : ℤ)) := by
  have e : ((m : ℕ) : v.1.adicCompletion ℚ) = algebraMap ℤ (v.1.adicCompletion ℚ) (m : ℤ) := by simp
  rw [e, IsScalarTower.algebraMap_apply ℤ ℚ (v.1.adicCompletion ℚ)]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v.1 _

theorem val_eval_eq_one (c : AfP p) (u : ℕ → ℕ)
    (h : ∀ n : ℕ, 0 < n → n.Coprime p → (u n).Coprime n ∧ ∃ β : AfP p, IsIntAf β ∧ c = (u n : AfP p) + n • β)
    (v : AwayP p) : Valued.v (AfP.eval v c) = 1 := by
  obtain ⟨l, hl0, hlp, hlv⟩ := exists_nat_mem v
  obtain ⟨hcop, β, hβ, e⟩ := h l hl0 hlp
  have hlt : Valued.v ((l : ℕ) : v.1.adicCompletion ℚ) < 1 := by
    rw [val_natCast, HeightOneSpectrum.valuation_lt_one_iff_mem]; exact hlv
  have hu : Valued.v ((u l : ℕ) : v.1.adicCompletion ℚ) = 1 := by
    rw [val_natCast]
    refine le_antisymm (HeightOneSpectrum.valuation_le_one _ _) (not_lt.1 fun hlt' => ?_)
    rw [HeightOneSpectrum.valuation_lt_one_iff_mem] at hlt'
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
    exact v.1.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hab ▸ add_mem (Ideal.mul_mem_left _ a hlt') (Ideal.mul_mem_left _ b hlv)))
  have hsmall : Valued.v (AfP.eval v (l • β)) < 1 := by
    rw [map_nsmul, nsmul_eq_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (hβ v)) hlt
  rw [e, map_add (f := _), map_natCast]
  rw [Valuation.map_add_eq_of_lt_left _ (by rw [hu]; exact hsmall), hu]

theorem exists_mul_eq_one : ∀ (p : ℕ) [Fact p.Prime] (c : AfP p) (u : ℕ → ℕ),
    (∀ n : ℕ, 0 < n → n.Coprime p → (u n).Coprime n ∧ ∃ β : AfP p, IsIntAf β ∧ c = (u n : AfP p) + n • β) →
    ∃ c' : AfP p, c * c' = 1 := by
  intro p _ c u h
  have hv := val_eval_eq_one c u h
  have hint : ∀ v : AwayP p, (AfP.eval v c)⁻¹ ∈ v.1.adicCompletionIntegers ℚ := fun v => by
    show Valued.v (AfP.eval v c)⁻¹ ≤ 1
    rw [map_inv₀, hv v, inv_one]
  let c' : AfP p := ⟨fun v => (AfP.eval v c)⁻¹, Filter.Eventually.of_forall hint⟩
  refine ⟨c', Subtype.ext (funext fun v => ?_)⟩
  have hne : AfP.eval v c ≠ 0 := fun h0 => by simpa [h0] using hv v
  exact mul_inv_cancel₀ hne

end GlobalTheory.AfUnit
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct

namespace GlobalTheory.LKGeo

theorem baseChangeAlgebraRepresentationAction_injective {C V : Type} [Ring C] [Algebra ℚ C] [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    (rep : C →ₐ[ℚ] Module.End ℚ V) (hrep : Function.Injective rep) (R : Type) [CommRing R] [Algebra ℚ R] :
    Function.Injective (actOn rep R) := by
  classical
  set b := Module.finBasis ℚ V
  let g : C →ₗ[ℚ] (Fin (Module.finrank ℚ V) × Fin (Module.finrank ℚ V) → ℚ) :=
    LinearMap.pi (fun ij => (b.coord ij.2).comp ((LinearMap.applyₗ (b ij.1)).comp rep.toLinearMap))
  have hg : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    apply hrep
    rw [map_zero]
    refine b.ext (fun i => b.ext_elem (fun j => ?_))
    have := congrFun hx (i, j)
    simpa [g] using this
  have hlg : Function.Injective (LinearMap.lTensor R g) :=
    Module.Flat.lTensor_preserves_injective_linearMap g hg
  have key : ∀ (y : R ⊗[ℚ] C) (i j : Fin (Module.finrank ℚ V)),
      TensorProduct.piScalarRight ℚ R R _ (LinearMap.lTensor R g y) (i, j) =
        TensorProduct.rid ℚ R (LinearMap.lTensor R (b.coord j) (actOn rep R y ((1 : R) ⊗ₜ b i))) := by
    intro y i j
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r x =>
      have h1 : actOn rep R (r ⊗ₜ x) ((1 : R) ⊗ₜ b i) = r ⊗ₜ (rep x (b i)) := by
        simp only [actOn, Algebra.TensorProduct.lift_tmul, Module.End.mul_apply]
        change r • ((rep x).baseChange R ((1 : R) ⊗ₜ b i)) = _
        rw [LinearMap.baseChange_tmul, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      rw [h1]
      simp [g, Algebra.smul_def]
    | add y z hy hz => simp only [map_add (f := _), Pi.add_apply, LinearMap.add_apply, hy, hz]
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro y hy
  apply hlg
  rw [map_zero]
  apply (TensorProduct.piScalarRight ℚ R R _).injective
  rw [map_zero]
  funext ij
  rw [key, hy]
  simp

theorem actOn_rep_afP_injective : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G),
    Function.Injective (actOn L.rep (AfP p)) := by
  intro p _ D G L
  haveI := D.finLa
  exact baseChangeAlgebraRepresentationAction_injective L.rep L.rep_inj (AfP p)

end GlobalTheory.LKGeo
end
