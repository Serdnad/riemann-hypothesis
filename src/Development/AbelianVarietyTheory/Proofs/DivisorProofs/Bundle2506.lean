module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle404
public import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle456
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2484
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2322
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2122
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1945
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1332
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1923
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2284
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2281
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1800
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
public import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2385
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2481
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2492
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2483
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2485
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2486
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2487
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1910
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2443
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Filter Topology
open scoped GlobalTheory.VacAny

namespace GlobalTheory.WeilTransfer

theorem transfer : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, X.Good v →
    ∃ t : E →ₐ[F] Fv F v, ∃ (ι : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ))
      (ν₀ : (Fv F v)ˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν₀ ∧ GlobalTheory.SmGL.IsUnitaryChar ν₀ ∧
      Set.BijOn ι (SB (Fin a' × Fin (a + a') → Fv F v) : Set _) (SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)) : Set _) ∧
      (∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), φ ∈ G.M'.SoLoc B.ψ t ↔
        ∀ Y : Matrix (Fin a') (Fin (a + a')) (Fv F v), Y.rank ≠ a' → ι φ Y = 0) ∧
      (∀ g₀ : GL (Fin a') (Fv F v), ∃ g ∈ UAt σ G.V' (evFin F v), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (g, 1)) φ φ₁ ∧
          ι φ₁ = GlobalTheory.FullRankCoinv.lact ν₀ g₀ (ι φ)) ∧
      ∀ h₀ : GL (Fin (a + a')) (Fv F v), ∃ h ∈ UAt σ G.W (evFin F v), ∃ c : ℂ, c ≠ 0 ∧
        ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
          Acts (evFin F v) (om' (1, h)) φ φ₁ ∧ ι φ₁ = c • fun Y => ι φ (Y * h₀.1) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT v hv
  have hcm : IsCMExt F E σ := hT.base.cm
  obtain ⟨t⟩ : Nonempty (E →ₐ[F] Fv F v) := GlobalTheory.T.split_place_embedding_exists F E σ hcm v hv.2
  let B' : Base F E := { B with v₁ := v, τ₁ := t }
  have hT' : IsTriple B' G X om om' :=
    { base := { hT.base with }
      geo := { hT.geo with hV := { hT.geo.hV with }, hV' := { hT.geo.hV' with }, hW := { hT.geo.hW with } }
      chars := { hT.chars with good := hv }
      weil := hT.weil
      weil' := hT.weil' }
  obtain ⟨ι, hι⟩ := GlobalTheory.T.exists_linear_bar_good_place hP F E σ B a a' G X om om' hT v hv t
  have hι' : G.M'.IsLinBar B'.ψ B'.τ₁ 1 1 ι := hι

  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hdet : IsUnit (G.V'.J.map t).det :=
    GlobalTheory.SplitUnitLift.isUnit_det_of_cartan G.V'.J t (B.emb w).1 1 one_ne_zero (G.V'.θ w)
      (by rw [one_smul]; exact hT.geo.hV'.cartan w)
  have herm : ∀ i j, σ (G.V'.J j i) = algebraMap F E 1 * G.V'.J i j := fun i j => by
    rw [map_one, one_mul]; exact hT.geo.hV'.herm i j
  let K := GlobalTheory.SplitUnitLift.liftU hcm t G.V'.J 1 herm hdet
  have hK : ∀ g, K g ∈ UAt σ G.V' (evFin F B'.v₁) ∧ (mat (K g)).map (piW B'.τ₁) = g.val ∧
      (mat (K g)).map (piW (B'.τ₁.comp σ)) = (G.V'.J.map B'.τ₁)⁻¹ * ((g⁻¹ : GL _ _).val)ᵀ * G.V'.J.map B'.τ₁ :=
    fun g => ⟨GlobalTheory.SplitUnitLift.liftU_mem_UAt hcm t G.V' 1 herm hdet g, GlobalTheory.SplitUnitLift.liftU_piW hcm t G.V'.J 1 herm hdet g,
      GlobalTheory.SplitUnitLift.liftU_piW_comp hcm t G.V'.J 1 herm hdet g⟩

  choose S hS using fun g => GlobalTheory.T.weilRepresentationLocality_unitaryGroupV' B G X om om' hT v (K g) (hK g).1
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (Fin a' × Fin (a + a')) v
  have eqR : ∀ φ₁ φ₂ : (Fin a' × Fin (a + a') → Fv F v) → ℂ, tens (evFin F v) φ₁ R = tens (evFin F v) φ₂ R → φ₁ = φ₂ := by
    intro φ₁ φ₂ h
    have hRc := (hR 0 (Submodule.zero_mem _)).1
    funext y
    have hp : At (evFin F v) (fun i => GlobalTheory.LatVac.liftV v (y i)) := fun u hu => funext fun i => GlobalTheory.LatVac.at_liftV v _ u hu
    have e := congrFun h (fun i => GlobalTheory.LatVac.liftV v (y i))
    have e2 : R (fun i => GlobalTheory.LatVac.liftV v (y i)) = R 0 := by simpa using hRc 0 _ hp
    simp only [tens, GlobalTheory.LatVac.evFin_liftV, e2] at e
    exact mul_right_cancel₀ hR0 e
  have hSR : ∀ g, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), om' (K g, 1) (tens (evFin F v) φ R) = tens (evFin F v) (S g φ) R :=
    fun g φ hφ => (hS g φ hφ).2 R (hR φ hφ)
  have h1 : ∀ g, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), S g φ ∈ SB _ := fun g φ hφ => (hS g φ hφ).1
  have tensLin : ∀ (c : ℂ) (φ φ' : (Fin a' × Fin (a + a') → Fv F v) → ℂ),
      tens (evFin F v) (c • φ + φ') R = c • tens (evFin F v) φ R + tens (evFin F v) φ' R := by
    intro c φ φ'; funext x; simp only [tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hlin : ∀ g, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ' ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ c : ℂ,
      S g (c • φ + φ') = c • S g φ + S g φ' := by
    intro g φ hφ φ' hφ' c
    have hm : c • φ + φ' ∈ SB (Fin a' × Fin (a + a') → Fv F v) := Submodule.add_mem _ (Submodule.smul_mem _ c hφ) hφ'
    apply eqR
    rw [← hSR g _ hm, tensLin, map_add (f := _), map_smul, hSR g φ hφ, hSR g φ' hφ', tensLin]
  have h2 : ∀ g g', ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), S (g * g') φ = S g (S g' φ) := by
    intro g g' φ hφ
    apply eqR
    have e1 : ((K (g * g'), (1 : UA σ G.W.J))) = (K g, 1) * (K g', 1) := by rw [map_mul, Prod.mk_mul_mk, one_mul]
    rw [← hSR _ φ hφ, e1, map_mul, Module.End.mul_apply, hSR g' φ hφ, hSR g _ (h1 g' φ hφ)]
  have h3 : ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), S 1 φ = φ := by
    intro φ hφ
    apply eqR
    have e1 : ((K 1, (1 : UA σ G.W.J))) = 1 := by rw [map_one]; rfl
    rw [← hSR _ φ hφ, e1, map_one, Module.End.one_apply]
  have hSplit := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hT.weil'
  have atAct : ∀ g (γ : Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), At (evFin F v) γ →
      At (evFin F v) (GlobalTheory.WeilM.actAB (cA σ) (K g, (1 : UA σ G.W.J)) γ) := by
    intro g γ hγ u hu
    simp only [GlobalTheory.WeilM.actAB]
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hγ u hu, Matrix.mul_zero, Matrix.zero_mul]
  have restS : ∀ g φ r, φ ∈ SB (Fin a' × Fin (a + a') → Fv F v) → Rest (evFin F v) φ r → Rest (evFin F v) (S g φ) r :=
    fun g φ r hφ hr => ⟨hr.1, by rw [← (hS g φ hφ).2 r hr]; exact hSplit.pres _ _ hr.2⟩
  have h4 : ∀ g (γ : Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), At (evFin F v) γ → ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        S g (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v γ) φ) =
          GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v)
            (GlobalTheory.LatVac.locCo G.M'.co v (GlobalTheory.WeilM.actAB (cA σ) (K g, (1 : UA σ G.W.J)) γ)) (S g φ) := by
    intro g γ hγ φ hφ
    have hw := GlobalTheory.T.schrodinger_preserves_schwartz_bruhat B.ψ hT.base.std.1 v (GlobalTheory.LatVac.locCo G.M'.co v γ) φ hφ
    refine GlobalTheory.T.eq_of_componentTensorAdelicFunction_eq v φ _ _ hφ fun r hr => ?_
    have hb1 := GlobalTheory.T.adelicHeisenberg_acts_by_local_schrodinger G.M'.co B.ψ v γ hγ φ r hr
    have hRw : Rest (evFin F v) (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v γ) φ) r :=
      ⟨hr.1, by rw [← hb1]; exact GlobalTheory.T.weil_representation_preserves_schwartz G.M' B.ψ hT.base.std γ _ hr.2⟩
    rw [← (hS g _ hw).2 r hRw, ← hb1, hSplit.impl _ _ _ hr.2, (hS g φ hφ).2 r hr,
      GlobalTheory.T.adelicHeisenberg_acts_by_local_schrodinger G.M'.co B.ψ v _ (atAct g γ hγ) (S g φ) r (restS g φ r hφ hr)]
  have h5 : ∀ g, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ∀ μ : @MeasureTheory.Measure (Fin a' × Fin (a + a') → Fv F v) (borel _),
      @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∫⁻ y, ‖S g φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ :=
    fun g φ hφ μ hμ => GlobalTheory.T.localWeilOperator_isometry_schwartzBruhat B G X om om' hT v (K g) (hK g).1 φ (S g φ) hφ (h1 g φ hφ) (hS g φ hφ).2 μ hμ
  obtain ⟨ν, α, hν, hC⟩ := GlobalTheory.T.heisenbergIntertwiner_eq_twisted_weilOperator B' G X om om' hT' K hK S h1 hlin h2 h3 h4 h5
  obtain ⟨hψc, hψ1, wT, wM, hA⟩ := GlobalTheory.T.linearModel_heisenbergOperators_translation_char B' G X om om' hT' K hK S h1 h4
  obtain ⟨hTι, hMι, -, -⟩ := hA ι hι'

  have hvac := hT.geo.hM'.vac v
  have hιv : ι (G.M'.vac v) ≠ 0 := fun h0 =>
    hvac.2.1 (hι.bij.injOn hvac.1 (Submodule.zero_mem _) (by rw [h0, map_zero]))
  obtain ⟨Y₀, hY₀⟩ := Function.ne_iff.mp hιv
  set φ₀ := GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B'.ψ B'.v₁) (wT Y₀) (G.M'.vac v) with hφ₀def
  have hφ₀ : φ₀ ∈ SB (Fin a' × Fin (a + a') → Fv F v) := GlobalTheory.T.schrodinger_preserves_schwartz_bruhat B.ψ hT.base.std.1 v _ _ hvac.1
  have hφ₀0 : ι φ₀ 0 ≠ 0 := by
    have e := congrFun (hTι Y₀ _ hvac.1) 0
    simp only [zero_add] at e
    rw [e]; exact hY₀

  obtain ⟨-, -, hcont⟩ := GlobalTheory.T.theta_action_exists hP F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' G.q (a' - G.q)
    (a + a' - (G.p + G.q)) (G.p + G.q) (GlobalTheory.ThK.Inhab.pairV' hT) v
  obtain ⟨U, hU, hUact⟩ := hcont φ₀ hφ₀
  have hKt : Tendsto K (𝓝 1) (𝓝 1) := GlobalTheory.T.split_unitary_lift_tendsto_one hcm t G.V'.J 1 herm hdet
  have hP1 : {g : GL (Fin a') (Fv F v) | (K g, (1 : UA σ G.W.J)) ∈ U} ∈ 𝓝 1 :=
    (hKt.prodMk_nhds tendsto_const_nhds) hU
  have hone : (1 : UA σ G.W.J) ∈ UAt σ G.W (evFin F v) := fun u _ => by simp [mat]
  have hsm : ∀ g ∈ {g : GL (Fin a') (Fv F v) | (K g, (1 : UA σ G.W.J)) ∈ U},
      (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) * GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) ((Fintype.card (Fin (a + a')) : ℂ) / 2) = 1 := by
    intro g hg
    have hact := hUact (K g, 1) hg (hK g).1 hone
    have hfix : S g φ₀ = φ₀ := eqR _ _ (by rw [← hSR g φ₀ hφ₀]; exact hact R (hR φ₀ hφ₀))
    have e := congrFun (hC ι hι' g φ₀ hφ₀) 0
    rw [hfix] at e
    simp only [GlobalTheory.SplitFlip.omB, map_one, Units.val_one, mul_one, GlobalTheory.SplitFlip.apow_one, Matrix.mul_zero,
      Matrix.zero_mul] at e
    have e2 : ι φ₀ 0 * 1 = ι φ₀ 0 * ((ν (GlobalTheory.SplitFlip.gdet g) : ℂ) *
        GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) ((Fintype.card (Fin (a + a')) : ℂ) / 2)) := by
      rw [mul_one]; nth_rw 1 [e]; ring
    exact (mul_left_cancel₀ hφ₀0 e2).symm
  have hsmooth : GlobalTheory.SmGL.IsSmoothChar ν := GlobalTheory.T.smooth_character_of_trivial_near_one (by have := (GlobalTheory.ThK.Inhab.two_le_rank hT).1; omega) ν _ _ hP1 hsm

  have hSo : ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), φ ∈ G.M'.SoLoc B.ψ t ↔
      ∀ Y : Matrix (Fin a') (Fin (a + a')) (Fv F v), Y.rank ≠ a' → ι φ Y = 0 := by
    intro φ hφ
    constructor
    · rintro ⟨-, ι₂, hι₂, hvan⟩ Y hY
      have hι₂' : G.M'.IsLinBar B'.ψ B'.τ₁ 1 1 ι₂ := hι₂
      obtain ⟨hT₂, hM₂, -, -⟩ := hA ι₂ hι₂'
      obtain ⟨c, hc⟩ := GlobalTheory.T.eq_smul_of_commute_heisenberg_linearModel_schwartzBruhat (SB (Fin a' × Fin (a + a') → Fv F v)) (GlobalTheory.LatVac.psiAt B'.ψ B'.v₁) hψc hψ1 ι₂ ι
        hι₂.bij (fun x _ y _ c => by rw [map_add (f := _), map_smul])
        (fun C => GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B'.ψ B'.v₁) (wT C))
        (fun l => GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B'.ψ B'.v₁) (wM l))
        (fun C x hx => ⟨GlobalTheory.T.schrodinger_preserves_schwartz_bruhat B.ψ hT.base.std.1 v _ x hx, hT₂ C x hx, hTι C x hx⟩)
        (fun l x hx => ⟨GlobalTheory.T.schrodinger_preserves_schwartz_bruhat B.ψ hT.base.std.1 v _ x hx, hM₂ l x hx, hMι l x hx⟩)
      rw [hc φ hφ, Pi.smul_apply, hvan Y hY, smul_zero]
    · intro h
      exact ⟨hφ, ι, hι, h⟩
  refine ⟨t, ι, ν, hsmooth, hν, hι.bij, hSo, fun g₀ => ⟨K g₀, (hK g₀).1, fun φ hφ =>
    ⟨S g₀ φ, h1 g₀ φ hφ, (hS g₀ φ hφ).2, ?_⟩⟩, GlobalTheory.T.linear_bar_functional_good_place hP F E σ B a a' G X om om' hT v hv t ι hι⟩
  rw [hC ι hι' g₀ φ hφ]
  funext Y
  simp only [GlobalTheory.SplitFlip.omB, GlobalTheory.FullRankCoinv.lact, map_one, Units.val_one, mul_one, GlobalTheory.SplitFlip.apow_one,
    Matrix.mul_one, Fintype.card_fin]

end GlobalTheory.WeilTransfer
end

section

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.componentImageDegree_between_of_proportionality : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), UnfAll U → Proport U → EqVolume U → ∀ u : Weight Dw, (∀ τ, StrictAnti (u τ)) → (∀ τ, StrictAnti (uPrime Dw u τ)) → (∀ Z, BirOn U Z (wtOf Dw u 0)) → (∀ Z, ValMult U Z (wtOf Dw u 0) (wtOf Dw (uPrime Dw u) 0)) → ∀ Z Z' : Comp Xo c, delPrime U Z' u ≤ compDeg U Z (wtOf Dw u 0) ∧ (compDeg U Z (wtOf Dw u 0) : ℝ) ≤ delPrime U Z' u / (1 - rhoB Dw u) := by
  first | exact @GlobalTheory.DegVal.compDeg_between | exact GlobalTheory.DegVal.compDeg_between | (intros; apply GlobalTheory.DegVal.compDeg_between <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares

namespace GlobalTheory.ShareOn.Reading

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Main2
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}


open GlobalTheory.OnTies in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in
theorem reading_of_runModel (p : PtAt ex Csz) (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r) (i : Fin D.R.m) {C : Type}
    [Finite C] [MulAction p.P.Gp C] (M : TwoLevels D.host.E D.R.r p.P.Gp C) (ka : Wt M.Ψ D.R.r)
    (hb0 : 0 < badN D) (hn : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV) (hM : RunModel p r h i M ka) :
    M.Ψ.card = D.R.f ∧ ∃ (ρ : Representation ℂ p.P.Gp (M.cusp ka)) (σ : D.what₂.LL →+* ℂ)
      (f : (Fin (p.R.toRealDat.nW i) → D.what₂.LL) →ₛₗ[σ] M.cusp ka),
      IsPullRep M ka ρ ∧ (∀ g v, ρ g (f v) = f ((p.R.toRealDat.FW i).ρ g v)) ∧
      (LinearIndependent ℂ fun k => f (Pi.single k 1)) ∧ Submodule.span ℂ (Set.range f) = ⊤ := by
  refine ⟨card_of_runModel hM, ?_⟩
  obtain ⟨v, e, ha, hb, hc, -⟩ := hM
  obtain ⟨act, hact, hcu⟩ := h.action v i

  let Rd : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i) →ₛₗ[(r.used v).full.σ₀] M.cusp ka :=
    LinearMap.codRestrict (M.cusp ka) (rdLin h ha) fun F => Submodule.subset_span ⟨_, GlobalTheory.T.usedRunCuspForm_reading_mem_modelCuspForms h ha hb F, rfl⟩
  have hRd : ∀ F, ((Rd F : M.cusp ka) : C → M.dom → ℂ) = rdLin h ha F := fun F => rfl
  letI : Algebra (r.used v).full.J.Q.c.F D.what₂.LL := p.alg
  obtain ⟨σ, hσ⟩ := exists_ext_embedding (K := (r.used v).full.J.Q.c.F) (LL := D.what₂.LL) (r.used v).full.σ₀
  let cu := cuspTo (h.laws v).p (fw2 p) i
  have hcuW : ∀ F, cu F ∈ ((R2 p).FW i).WK := fun F => ((fw2 p).e i _).2
  have hcuinj : Function.Injective cu := by
    intro F G hFG
    have h1 := Subtype.ext hFG
    have h2 := ((fw2 p).e i).injective h1
    exact Submodule.inclusion_injective _ h2
  have hsurj : ∀ w ∈ ((R2 p).FW i).WK, ∃ F, cu F = w := by
    intro w hw
    refine ⟨⟨(((fw2 p).e i).symm ⟨w, hw⟩).1, by
      rw [cutR_eq _ (inR_succ i)]; exact (((fw2 p).e i).symm ⟨w, hw⟩).2⟩, ?_⟩
    show ((((fw2 p).e i) _ : ((R2 p).FW i).WK) : Fin _ → D.what₂.LL) = w
    exact congrArg Subtype.val (LinearEquiv.apply_symm_apply ((fw2 p).e i) ⟨w, hw⟩)
  obtain ⟨m, b', hbW, hbK, hspK, hbL, hspL⟩ := (fw2 p).ks i
  choose bC hbC using fun k => hsurj (b' k) (hbW k)
  have hbC' : (fun k => cu (bC k)) = b' := funext hbC
  have hbs : Submodule.span (recB (h.laws v).p.toLawsCore).KO (Set.range bC) = ⊤ := by
    rw [eq_top_iff]
    intro F _
    have h1 : cu F ∈ Submodule.span p.T.Q.c.F (Set.range b') := by rw [hspK]; exact hcuW F
    obtain ⟨cf, hcf⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h1
    have h2 : cu (∑ k, (show (recB (h.laws v).p.toLawsCore).KO from cf k) • bC k) = cu F := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, ← hcf]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, hbC k]
      rfl
    rw [← hcuinj h2]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have hbi : LinearIndependent D.what₂.LL (fun k => cu (bC k)) := by rw [hbC']; exact hbL
  have hbt : Submodule.span D.what₂.LL (Set.range fun k => cu (bC k)) = ⊤ := by rw [hbC']; exact hspL
  have hK : LinearIndependent (recB (h.laws v).p.toLawsCore).KO bC := by
    apply LinearIndependent.of_comp cu
    show LinearIndependent _ (fun k => cu (bC k))
    rw [hbC']; exact hbK
  have hR : LinearIndependent ℂ (fun k => Rd (bC k)) :=
    LinearIndependent.of_comp (M.cusp ka).subtype (GlobalTheory.T.cuspForm_family_linearIndependent h ha m bC hK)
  have hRs : Submodule.span ℂ (Set.range Rd) = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨y, hy⟩ -
    have hy' : y ∈ (Submodule.span ℂ (Set.range Rd)).map (M.cusp ka).subtype := by
      rw [Submodule.map_span, ← Set.range_comp]
      unfold TwoLevels.cusp at hy
      refine Submodule.span_le.2 ?_ hy
      rintro _ ⟨G, hG, rfl⟩
      obtain ⟨m', α, Fs, hGe⟩ := GlobalTheory.T.modelCuspForms_span_usedRunReadings h ha hb hb0 hn G hG
      have hGs : M.res G = ∑ k, α k • rdLin h ha (Fs k) := by
        funext c x
        simp only [TwoLevels.res, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, rdLin_apply]
        exact hGe c x.1 x.2
      rw [hGs]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fs k, rfl⟩)
    obtain ⟨z, hz, hzy⟩ := hy'
    have hz' : z = ⟨y, hy⟩ := Subtype.ext hzy
    rw [← hz']; exact hz
  obtain ⟨f, ρ, hfcu, hint, hind, hspan⟩ := GlobalTheory.T.exists_semilinear_extension_of_form_with_transported_rep (r.used v).full.σ₀ σ hσ cu bC hbs hbi hbt Rd hR hRs ((R2 p).FW i).ρ
  have hρR : ∀ g F, ρ g (Rd F) = Rd (act g F) := by
    intro g F
    rw [← hfcu, ← hfcu, hint, hcu g F]
  obtain ⟨a, hpull⟩ := hc
  refine ⟨ρ, σ, f, ⟨a, fun g G hG c x => ?_⟩, hint, hind, hspan⟩
  obtain ⟨m', α, Fs, hGe⟩ := GlobalTheory.T.modelCuspForms_span_usedRunReadings h ha hb hb0 hn G hG
  have hy : (⟨M.res G, Submodule.subset_span ⟨G, hG, rfl⟩⟩ : M.cusp ka) = ∑ k, α k • Rd (Fs k) := by
    apply Subtype.ext
    funext c' x'
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, TwoLevels.res, hRd,
      rdLin_apply]
    exact hGe c' x'.1 x'.2
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hy, map_sum]
  simp only [map_smul, hρR, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hRd,
    rdLin_apply]
  rw [TwoLevels.pull, hGe (g • c) _ (GlobalTheory.T.twoLevelFlagDomain_transporter_mem_domain M g c x.1 x.2), Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk := hpull (Fs k) g c x.1 x.2 (psi_eq ha c) (psi_eq ha (g • c))
  rw [rdLin_apply]
  unfold rdFun rdR
  rw [hact g⁻¹ (Fs k)]
  refine (congrArg (α k * ·) hk).trans ?_
  ring
end Main2

end GlobalTheory.ShareOn.Reading
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem _root_.GlobalTheory.T.exists_affine_snc_chart_cartier_single_equation : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q] (B : Closeds Y), FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B) → ∀ (A : CartierDiv Y) (ι : Type) (s : ι → Y.functionField), (∀ i, s i ∈ A.sections) → ∀ y₀ : Y, ∃ (W : Y.Opens) (hW : y₀ ∈ W) (z : Fin n → Γ(Y, W)) (w : Fin n → Y) (u : Fin n → Y.functionFieldˣ) (e : Y.functionFieldˣ) (f : ι → Γ(Y, W)), IsFrame (dOn q z) ∧ (∀ y ∈ W, A.IsEqn y e) ∧ (∀ i, fnOf W (gen_mem hW) (f i) = s i * e) ∧ ∀ (y : Y) (hy : y ∈ W), ∃ J : Finset (Fin n), IsSncChart q n B y W hy z J w u ∧ ∀ j ∈ J, y ∉ Y.basicOpen (z j) := by
  first | exact @GlobalTheory.PairStep.exists_sncChart_isEqn_affine | exact GlobalTheory.PairStep.exists_sncChart_isEqn_affine | (intros; apply GlobalTheory.PairStep.exists_sncChart_isEqn_affine <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

theorem compatibleForms_cocycles_differ_by_coboundary : ∀ (R R' : Type) [CommRing R] [CommRing R'] (I : Ideal R) (I' : Ideal R') (κ : DividedPowers I) (κ' : DividedPowers I') (X X' : Scheme.{0}) (t : X ⟶ Sp R) (t' : X' ⟶ Sp R') (σ : R →+* R') (φ₀ : X' ⟶ X) (m : IsMor κ t κ' t' σ φ₀) (k : (KK κ t).Z1) (k' : (KK κ' t').Z1) (f : Z1 (O κ t)) (f' : Z1 (O κ' t')), k.1.1 = f.1 → k'.1.1 = f'.1 → H1.mk _ f' = m.pull1 (H1.mk _ f) → ∃ g, (KK κ' t').D0 g = (morMap m).p1 k.1 - k'.1 := by
  intro R R' _ _ I I' κ κ' X X' t t' σ φ₀ m k k' f f' hk hk' h
  have h' : H1.mk _ (m.coef.pullbackOneCocycle f) = H1.mk _ f' := h.symm
  obtain ⟨g, hg⟩ := H1.mk_eq_mk.1 h'
  have hinj := (GlobalTheory.T.fnMap_pullbackBijective12_kk_and_res R' I' κ' X' t' X' (𝟙 X')).1.1.injective
  have hz : (morMap m).p1 k.1 - k'.1 ∈ (KK κ' t').Z1 :=
    sub_mem ((morMap m).z1 k).2 k'.2
  have h0 : (KK κ' t').fnMap.h1 (QuotientAddGroup.mk ⟨_, hz⟩ : (KK κ' t').H1) = 0 := by
    change (QuotientAddGroup.mk ((KK κ' t').fnMap.z1 ⟨_, hz⟩) : Cx.H1 _) = 0
    rw [QuotientAddGroup.eq_zero_iff]
    refine ⟨g, ?_⟩
    refine Prod.ext ?_ ?_
    · funext T T' φ
      have e := congrFun (congrFun (congrFun hg T) T') φ
      have e1 := congrFun (congrFun (congrFun hk (m.obj T)) (m.obj T')) (m.functor.map φ)
      have e2 := congrFun (congrFun (congrFun hk' T) T') φ
      refine e.trans ?_
      exact congrArg₂ (fun u v : T'.B ↦ u - v) e1.symm e2.symm
    · funext T
      rfl
  have h1 := hinj (h0.trans (map_zero (KK κ' t').fnMap.h1).symm)
  rw [QuotientAddGroup.eq_zero_iff] at h1
  exact h1

end GlobalTheory.PDForm
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm.ClsTwo

universe u

theorem cob_of_fn_cob {C : Type u} [Category.{0} C] (K : Cx C) (h : Function.Injective K.fnMap.h2)
    (z : K.T2) (hz : z ∈ K.Z2) (e : K.M0.c1)
    (he : ∀ T T' T'' (φ : T ⟶ T') (ψ : T' ⟶ T''),
      K.M0.map ψ (e T T' φ) - e T T'' (φ ≫ ψ) + e T' T'' ψ = z.1 T T' T'' φ ψ) :
    ∃ g, K.D1 g = z := by
  have h0 : K.fnMap.h2 (QuotientAddGroup.mk ⟨z, hz⟩) = 0 := by
    change (QuotientAddGroup.mk (K.fnMap.z2 ⟨z, hz⟩) : (Cx.single K.M0).H2) = 0
    rw [QuotientAddGroup.eq_zero_iff]
    refine ⟨(e, 0), ?_⟩
    refine Prod.ext ?_ rfl
    funext T T' T'' φ ψ
    exact he T T' T'' φ ψ
  have h1 : (QuotientAddGroup.mk ⟨z, hz⟩ : K.H2) = 0 := h (h0.trans (map_zero _).symm)
  rw [QuotientAddGroup.eq_zero_iff] at h1
  exact h1

theorem cob_of_class_eq : ∀ (R R' : Type) [CommRing R] [CommRing R'] (I : Ideal R) (I' : Ideal R') (κ : DividedPowers I) (κ' : DividedPowers I') (X X' : Scheme.{0}) (t : X ⟶ Sp R) (t' : X' ⟶ Sp R') (σ : R →+* R') (φ₀ : X' ⟶ X) (m : IsMor κ t κ' t' σ φ₀) (k : (KK κ t).Z2) (k' : (KK κ' t').Z2) (f : Z2 (O κ t)) (f' : Z2 (O κ' t')), k.1.1 = f.1 → k'.1.1 = f'.1 → H2.mk _ f' = m.pull2 (H2.mk _ f) → ∃ g, (KK κ' t').D1 g = (morMap m).p2 k.1 - k'.1 := by
  intro R R' _ _ I I' κ κ' X X' t t' σ φ₀ m k k' f f' hk hk' h
  have h' : H2.mk _ (m.coef.pullbackTwoCocycle f) = H2.mk _ f' := h.symm
  obtain ⟨e, he⟩ := H2.mk_eq_mk.1 h'
  refine cob_of_fn_cob (KK κ' t') (GlobalTheory.T.fnMap_pullbackBijective12_kk_and_res R' I' κ' X' t' X' (𝟙 X')).1.2.injective _
    (AddSubgroup.sub_mem _ ((morMap m).p2_mem_Z2_of_mem_Z2 k.2) k'.2) e ?_
  intro T T' T'' φ ψ
  have h1 := congrFun (congrFun (congrFun (congrFun (congrFun he T) T') T'') φ) ψ
  refine h1.trans ?_
  have h2 : (m.coef.pullbackTwoCocycle f).1 T T' T'' φ ψ = ((morMap m).p2 k.1).1 T T' T'' φ ψ :=
    (congrFun (congrFun (congrFun (congrFun (congrFun hk _) _) _) (m.functor.map φ)) (m.functor.map ψ)).symm
  have h3 := congrFun (congrFun (congrFun (congrFun (congrFun hk' T) T') T'') φ) ψ
  exact congrArg₂ (fun a b : (O κ' t').obj T'' ↦ a - b) h2 h3.symm

end GlobalTheory.PDForm.ClsTwo
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_unitVacuum_standardLattices_definitePair : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} (N : GlobalTheory.FunObj.Std G U) (p : Pair T), GlobalTheory.FunObj.DefPair D.R.m p → ∃ f, IsVacO W.ψ W.θ _ _ (G.cartS W.cart p) (G.onT W.cart p) (N.latS p : Set _) (N.latT p : Set _) f := by
  first | exact @GlobalTheory.FunObj.vac_exists_of_defPair | exact GlobalTheory.FunObj.vac_exists_of_defPair | (intros; apply GlobalTheory.FunObj.vac_exists_of_defPair <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic

theorem _root_.GlobalTheory.T.exists_ample_sections_pullback_bound_of_genFinite : ∀ (F : Type) [Field F] (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (p : W ⟶ Sp F) (f : M ⟶ W), IsProjOver p → IsProjOver (f ≫ p) → Surjective f → f.residueDegree (genericPoint M) ≠ 0 → ∃ (r : ℕ) (A : LB W), IsAmpleLB A ∧ ∀ B : LB W, B.IsLB → (letI := algebraΓOfHom (f ≫ p); lbH0 F (B.pull f)) ≤ r * (letI := algebraΓOfHom p; lbH0 F (tens B A)) := by
  first | exact @GlobalTheory.GlobalSectionsPullback.globalSectionsDim_pullback_le_generically_finite | exact GlobalTheory.GlobalSectionsPullback.globalSectionsDim_pullback_le_generically_finite | (intros; apply GlobalTheory.GlobalSectionsPullback.globalSectionsDim_pullback_le_generically_finite <;> assumption)
end
