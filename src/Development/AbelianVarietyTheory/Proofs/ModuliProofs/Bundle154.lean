module

import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle149
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle097
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle029
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAdaptedLieBasis
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle140
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle108
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelAbelianSchemeConstOverDualNumbers
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle094
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelShapePrimitivityPullbackDescent
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle152
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle146
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle098
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNeZeroClosedFibre
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecPullNeZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle045
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle016
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.AlgebraLevelSetting
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.PelTangent

open GlobalTheory.ShapePull

def chartPullSection {X Y : Scheme.{0}} (L : LB X) (F : Y ⟶ X) (r : X ⟶ Y) (e : r ≫ F = 𝟙 X) :
    ChartPull L (L.pull F) r :=
  have m : ∀ i y, y ∈ L.U i → r y ∈ (L.pull F).U (fun _ => i) := fun i y hy => mem_pull.2 (by
    have : F (r y) = y := congrArg (fun g : X ⟶ X => g y) e
    rw [this]; exact hy)
  { idx := fun i _ => i
    le := fun i y hy => m i y hy
    g := fun y i j hi hj =>
      ((gm_pull_g L F r y (fun _ => i) (fun _ => j) (m i y hi) (m j y hj)).trans (by rw [e])).symm }

section Group

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

theorem exists_oAct (h : IsGrpPullback G' G f φ) {O : Type} [CommRing O] (a : OAct O G) :
    ∃ a' : OAct O G', ∀ c, (a'.act c).left ≫ φ = φ ≫ (a.act c).left := by
  choose w hw pa using fun c => (haveI := a.hom c; GlobalTheory.SymBaseChange.exists_endo h (a.act c))
  have hl : ∀ c, (w c).left ≫ φ = φ ≫ (a.act c).left := fun c => by
    have := congrArg (fun z => z.left) (pa c (𝟙 G'))
    simpa [pushPt] using this
  refine ⟨⟨w, hw, ?_, fun c d => ?_, fun c d => ?_⟩, hl⟩
  · exact eq_up h _ (push_end h (hl 1)) (push_id h) a.one
  · exact eq_up h _ (push_end h (hl _)) (push_comp h _ (push_end h (hl c)) (hl d)) (a.mul c d)
  · exact eq_up h _ (push_end h (hl _)) (push_mul h _ (push_end h (hl c)) (push_end h (hl d))) (a.add c d)

theorem adj_up [IsCommMonObj G] [IsCommMonObj G'] (h : IsGrpPullback G' G f φ) {L : LB G.left} {L' : LB G'.left}
    (hL : L.IsLB) (hL' : L'.IsLB) (H : LBIso L' (L.pull φ)) {w v : G ⟶ G} {w' v' : G' ⟶ G'}
    (hw : w'.left ≫ φ = φ ≫ w.left) (hv : v'.left ≫ φ = φ ≫ v.left)
    (A : LBIso (cubeLB G ![fst G G ≫ w, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ v] L)) :
    LBIso (cubeLB G' ![fst G' G' ≫ w', snd G' G'] L') (cubeLB G' ![fst G' G', snd G' G' ≫ v'] L') :=
  iso_up (DVR.linComb_isLB _ hL _ _) (DVR.linComb_isLB _ hL _ _) (DVR.linComb_isLB _ hL' _ _)
    (DVR.linComb_isLB _ hL' _ _) (iso_cubeLB_pull h _ H (push_comp h _ (push_fst h) hw) (push_snd h))
    (iso_cubeLB_pull h _ H (push_fst h) (push_comp h _ (push_snd h) hv)) A

theorem prim_up [IsCommMonObj G] [IsCommMonObj G'] (h : IsGrpPullback G' G f φ) {L : LB G.left} {L' : LB G'.left}
    (hL : L.IsLB) (hL' : L'.IsLB) (H : LBIso L' (L.pull φ)) {w : G ⟶ G} {w' : G' ⟶ G'}
    (hw : w'.left ≫ φ = φ ≫ w.left) (A : LBIso L (cubeLB G ![𝟙 G, w] L)) :
    LBIso L' (cubeLB G' ![𝟙 G', w'] L') := by
  have i : LBIso (cubeLB G' ![𝟙 G', w'] L') ((cubeLB G ![𝟙 G, w] L).pull φ) :=
    iso_cubeLB_pull h (selfMap h) H (push_id h) (push_end h hw)
  have a : (cubeLB G ![𝟙 G, w] L).IsLB := DVR.linComb_isLB _ hL _ _
  have a' : (cubeLB G' ![𝟙 G', w'] L').IsLB := DVR.linComb_isLB _ hL' _ _
  exact iso_up hL a hL' a' H i A

end Group

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cmHostUnit_add_conj_eq_one (H : Host E) : H.w0 + H.bar H.w0 = 1 := by
  apply GlobalTheory.Ex.Arch.AbVal.cmField_host_element_add_conj_eq_one <;> assumption

theorem spMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'')
    (h : R →+* R'') (e : g.comp f = h) : spMap g ≫ spMap f = spMap h := by
  subst e
  exact (Spec.map_comp _ _).symm

theorem tangent_le_dim : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) (a : J → 𝓞 E) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (ρ : o) (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (r : ℕ) (β : o →+* K) (t : TObj g k J b (spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β))) (τ : SAB H (Sp (TrivSqZeroExt K (Fin r → K)))), a w = H.w0 → a w' = H.bar H.w0 → ρ ^ 2 = -(H.d : o) → IsPEL D a bas ρ t τ → (∀ (lam : (Fin r → K) →ₗ[K] K) (t' : TObj g k J b (spMap ((algebraMap K (DualNumber K)).comp β))), TMap t' t (spMap (dirMap lam)) → TMap t' t (constPt (spMap (dirMap lam))) → lam = 0) → r ≤ D.dim := by
  intro L1 L2 L3 E _ _ _ H D g J a w w' bas k o _ b ρ K _ _ _ r β t τ hw hw' hρ ⟨e, he, hL, hact, hdet⟩ hlam
  letI := t.ab.comm
  let p : Sp K ⟶ Sp (TrivSqZeroExt K (Fin r → K)) := spMap (TrivSqZeroExt.fstHom K K (Fin r → K)).toRingHom
  let q : Sp K ⟶ Sp (DualNumber K) := spMap (TrivSqZeroExt.fstHom K K K).toRingHom
  have hp : p ≫ spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β) = spMap β :=
    spMap_comp _ _ _ (by ext x; simp [TrivSqZeroExt.algebraMap_eq_inl])
  obtain ⟨t₀, T₀⟩ := GlobalTheory.tObj_pull o g k J b _ _ _ _ p t hp
  obtain ⟨φ₀, h₀, hL₀, hpt₀, hact₀⟩ := id T₀
  letI := t₀.ab.comm

  have : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  have h₁ : IsGrpPullback t.A τ.G (𝟙 _) e.inv.left := isGrpPullback_of_iso e.symm
  have ih : e.inv.left ≫ e.hom.left = 𝟙 _ := by rw [← Over.comp_left, e.inv_hom_id, Over.id_left]
  have hL₁ : LBIso t.L (τ.PP.L.pull e.inv.left) :=
    LBIso.chartPull (chartPullSection t.L _ _ ih) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull τ.PP.L _ _ rfl) hL.symm
  obtain ⟨A, hA⟩ := exists_oAct h₁ τ.act
  obtain ⟨A₀, hA₀⟩ := exists_oAct h₀ A
  have hj : ∀ j, (t.act j).left ≫ e.inv.left = e.inv.left ≫ (τ.act.act (a j)).left := fun j => by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    rw [Iso.comp_inv_eq, Category.assoc, hact, e.inv_hom_id_assoc]
  have adj := fun c => adj_up h₁ τ.PP.isLB t.isLB hL₁ (hA c) (hA (H.bar c)) (τ.adj c)
  have prim : t.Prim w w' := by
    refine ⟨eq_up h₁ _ (push_mul h₁ _ (push_end h₁ (hj w)) (push_end h₁ (hj w'))) (push_id h₁) ?_,
      adj_up h₁ τ.PP.isLB t.isLB hL₁ (hj w) (hj w') ?_, prim_up h₁ τ.PP.isLB t.isLB hL₁ (hj w) ?_⟩
    · rw [hw, hw', ← τ.act.add, cmHostUnit_add_conj_eq_one, τ.act.one]
    · rw [hw, hw']; exact τ.adj _
    · rw [hw]; exact τ.prim
  have det : DetCond D A₀ (𝟙 (Sp K)) (β ρ) := fun σ => by
    have key : ∀ n, LieMult τ.act p σ n → LieMult A₀ (𝟙 (Sp K)) σ n := fun n hn =>
      (GlobalTheory.LiePull.lieMult_pull _ _ _ _ _ _ _ A A₀ h₀ hA₀ K _ σ n).2
        ((GlobalTheory.LiePull.lieMult_pull _ _ _ _ _ _ _ τ.act A h₁ hA K _ σ n).2 (by
          rw [Category.comp_id, Category.id_comp]; exact hn))
    have := (hdet K p β hp).1 σ
    exact ⟨fun x => key _ (this.1 x), fun x => key _ (this.2 x)⟩
  obtain ⟨n, v, ty, hv, hty, hdiag⟩ := GlobalTheory.exists_adapted_lieBasis E H D K t₀.A A₀ (β ρ) t₀.ab.smooth det
  obtain ⟨Θ, hsym, hcomm, hker⟩ := GlobalTheory.T.exists_ksMatrix_alt L1 L2 L3 K r t.pol t₀.pol φ₀ n v h₀ hL₀ hv
  have inj : Function.Injective Θ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro lam h0
    let d : Sp (DualNumber K) ⟶ Sp (TrivSqZeroExt K (Fin r → K)) := spMap (dirMap lam)
    have hd : d ≫ spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β) =
        spMap ((algebraMap K (DualNumber K)).comp β) :=
      spMap_comp _ _ _ (by ext x <;> simp [dirMap, TrivSqZeroExt.algebraMap_eq_inl])
    have hq : q ≫ d = p := spMap_comp _ _ _ (by ext x; simp [dirMap])
    obtain ⟨t', T'⟩ := GlobalTheory.tObj_pull o g k J b _ _ _ _ d t hd
    obtain ⟨ψ, h', hL', hpt', hact'⟩ := id T'
    letI := t'.ab.comm
    obtain ⟨ψ₀, k₀, k₁⟩ := hker lam h0 t'.A ψ h'
    let io : t₀.A.left ⟶ t'.A.left := h'.1.lift φ₀ (t₀.A.hom ≫ q) (by rw [h₀.1.w, Category.assoc, hq])
    have i₁ : io ≫ ψ = φ₀ := h'.1.lift_fst _ _ _
    have i₂ : io ≫ t'.A.hom = t₀.A.hom ≫ q := h'.1.lift_snd _ _ _
    have prim' : t'.Prim w w' :=
      ⟨eq_up h' _ (push_mul h' _ (push_end h' (hact' w)) (push_end h' (hact' w'))) (push_id h') prim.1,
        adj_up h' t.isLB t'.isLB hL' (hact' w) (hact' w') prim.2.1, prim_up h' t.isLB t'.isLB hL' (hact' w) prim.2.2⟩
    have c₁ : IsGrpPullback t₀.A t'.A q io := h'.cancel (h₀.congr hq.symm i₁.symm) i₂
    have c₂ : LBIso t₀.L (t'.L.pull io) :=
      LBIso.trans t₀.isLB (pull_isLB t.isLB φ₀) (pull_isLB t'.isLB io) hL₀
        (LBIso.chartPull (chartPullSame t.L _ _ _ io fun _ => i₁.symm) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull t'.L io io rfl) hL'.symm)
    have c₃ : ∀ i, (t₀.pt i).left ≫ io = q ≫ (t'.pt i).left := fun i => by
      apply h'.1.hom_ext
      · rw [Category.assoc, i₁, hpt₀, Category.assoc, hpt', ← Category.assoc, hq]
      · rw [Category.assoc, i₂, ← Category.assoc, Over.w, Category.assoc, Over.w]
        exact (Category.id_comp _).trans (Category.comp_id _).symm
    have c₄ : ∀ j, (t₀.act j).left ≫ io = io ≫ (t'.act j).left := fun j => by
      apply h'.1.hom_ext
      · rw [Category.assoc, i₁, hact₀, Category.assoc, hact', ← Category.assoc, i₁]
      · rw [Category.assoc, i₂, ← Category.assoc, Over.w, Category.assoc, Over.w, i₂]
    have T₁ := GlobalTheory.ConstTheta.tMap_of_const L1 L2 L3 o g k J b w w' K _ _ t' t₀ io ψ₀ prim' c₁ c₂ c₃ c₄ k₀ (k₁ io i₁ i₂)
    have T₂ := ((GlobalTheory.ZM.tmap_id_comp_cancel o g k J b _ _ _ _ _ _ t t₀ t').2 _ _ T₀).1 T₁
    refine hlam lam t' T' ?_
    show TMap t' t (_ ≫ q ≫ d)
    rw [hq]
    exact T₂
  have hρ' : β ρ ^ 2 = -(H.d : K) := by rw [← map_pow, hρ, map_neg, map_natCast]
  have B := GlobalTheory.SymSignature.finrank_le E H D.p D.q n K (β ρ) ty (LinearMap.range Θ) hρ' hty (by
    rintro _ ⟨lam, rfl⟩
    exact ⟨hsym lam, fun c => hcomm (A.act c) (A.act (H.bar c)) (A₀.act c) (A₀.act (H.bar c)) _ _ (A.hom _) (A.hom _)
      (hA₀ _) (hA₀ _) (adj c) (hdiag c) (hdiag (H.bar c)) lam⟩)
  rw [LinearMap.finrank_range_of_inj inj] at B
  simpa [Datum.dim, Module.finrank_linearMap] using B

end GlobalTheory.PelTangent
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.le_ringKrullDim_thetaFamily_genericFibre : Out.Laws → Out.Laws2 → ∀ (g n N' : ℕ) (J : Type) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (w w' : J) (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop) (d : ℕ) (F : WFam n em C Mat κ), 3 ≤ N' → Odd N' → ArBase em → GoodClass em C Mat κ w w' d → ∀ (R : Type) [CommRing R] [Algebra o R] (x : Sp R ⟶ F.U.toScheme), IsOpenImmersion x → x ≫ F.U.ι ≫ F.Y.s = spMap (algebraMap o R) → ∀ q ∈ minimalPrimes (FractionRing o ⊗[o] R), (d : WithBot ℕ∞) ≤ ringKrullDim ((FractionRing o ⊗[o] R) ⧸ q) := by
  first | exact @GlobalTheory.ZM.GenericDim.le_ringKrullDim_genericFibre | exact GlobalTheory.ZM.GenericDim.le_ringKrullDim_genericFibre | (intros; apply GlobalTheory.ZM.GenericDim.le_ringKrullDim_genericFibre <;> assumption)
end

section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UU
open GlobalTheory.IndefiniteRowSideFullHecke.AlgebraLevelSetting (SymTriv Level Step FormalTorus Lv pr torus_w)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UniformizationSetting

section Weights
variable {S A Y₁ Y₂ : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X] {i : splitTorus S X ⟶ G}
  {L : LB A}

end Weights

section Packages
variable {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [IsCommMonObj G] [GrpObj G']
  [IsCommMonObj G'] [GrpObj G''] [IsCommMonObj G''] {X : Type} [AddCommGroup X]

variable {P : CP G} {P' : CP G'} {P'' : CP G''} {f : S' ⟶ S} {f' : S'' ⟶ S'} {f'' : S'' ⟶ S}
  {F : G'.left ⟶ G.left} {F' : G''.left ⟶ G'.left} {F'' : G''.left ⟶ G.left} {hw : F ≫ G.hom = G'.hom ≫ f}

end Packages

section Triv
variable {S S' : Scheme.{0}} {G : Over S} {G' H : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  [GrpObj H] {P : CP G} {P' : CP G'} {f : S' ⟶ S} {F : G'.left ⟶ G.left} {hw : F ≫ G.hom = G'.hom ≫ f}
  {w : LB.Iso P'.L.L (P.L.L.pull F)} {i : H ⟶ G'}

variable {S'' : Scheme.{0}} {X : Type} [AddCommGroup X]

theorem exists_even_of_desc {Q : TQ G X} (D : Q.Desc P) : ∃ σ : CubTriv P.c Q.i, σ.Even := by
  have := Q.i_hom
  obtain ⟨s, hs, v⟩ := exists_gen D.M.L.isLB (φ := (PEmpty.elim : PEmpty → ((splitTorus S X).left ⟶ Q.B.left)))
    (ε := PEmpty.elim) (K' := Fin 2) (φ' := ![(1 : splitTorus S X ⟶ Q.B).left, (1 : splitTorus S X ⟶ Q.B).left])
    (ε' := ![1, -1]) (fun U _ h => by simp [Fin.prod_univ_two]) (LB.oneGen D.M.L.L)
    (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
  have v' : ∀ (Z : Scheme.{0}) r (z : Z) J, Good D.M.L.L z J → val s r z J = 1 := fun Z r z J hJ =>
    (v Z r z J hJ).trans (val_one _)
  have e : Q.i ≫ Q.q = 1 := Q.isKernel.w
  refine TowerEx.exists_even_pull D.map (e ▸ TorusCompat.of_comp Q.i Q.q : TorusCompat _ _ Q.i 1)
    ⟨s, hs, fun T x y u z J hJ => ?_⟩ fun T x z J hJ => ?_
  · simp only [v' _ _ z J hJ, MonObj.comp_one, _root_.mul_one]
    exact ((isCub_cubV D.M.c (T := T) hJ).face 1 1).symm
  · show val s _ z J = _ * val s _ z J
    rw [v' _ _ z J hJ, v' _ _ z J hJ, MonObj.comp_one, D.M.val_sym_one hJ, _root_.mul_one]

end Triv

theorem exists_tq_lift {A A' : Type} [CommRing A] [IsLocalRing A] [CommRing A'] [Nontrivial A']
    (hA : IsNilpotent (IsLocalRing.maximalIdeal A)) (φ : A →+* A') (hφ : Function.Surjective φ)
    {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G]
    [IsCommMonObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (G' : Over (Spec (CommRingCat.of A'))) [GrpObj G']
    [IsCommMonObj G'] {F : G'.left ⟶ G.left} (hF : IsGrpPullback G' G (Spec.map (CommRingCat.ofHom φ)) F)
    (Q' : TQ G' X) : ∃ Q : TQ G X, TorusCompat (Spec.map (CommRingCat.ofHom φ)) F Q'.i Q.i := by
  obtain ⟨Q, hQ, -⟩ := TowerEx.exists_lift hA φ hφ G G' hF (P := CP.triv G) (P' := CP.triv G')
    (IsCPMap.triv (hw := hF.1.w) (TowerEx.toBase_mul hF _)) Q' ⟨CubTriv.triv _, CubTriv.triv_even _⟩
  exact ⟨Q, hQ⟩

section Levels
variable {S S₁ S₂ : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {P : CP G} {X : Type} [AddCommGroup X]
  [Module.Free ℤ X] [Module.Finite ℤ X] {f₁ : S₁ ⟶ S} {f₂ : S₂ ⟶ S}
  {G₁ : Over S₁} [GrpObj G₁] [IsCommMonObj G₁] {F₁ : G₁.left ⟶ G.left} {h₁ : F₁ ≫ G.hom = G₁.hom ≫ f₁}
  {G₂ : Over S₂} [GrpObj G₂] [IsCommMonObj G₂] {F₂ : G₂.left ⟶ G.left} {h₂ : F₂ ≫ G.hom = G₂.hom ≫ f₂}
  [ConnectedSpace S₁] {L₁ : Level P X f₁ G₁ F₁ h₁} {L₂ : Level P X f₂ G₂ F₂ h₂} {t : S₁ ⟶ S₂} {m : G₁.left ⟶ G₂.left}


variable {B : Over S} [GrpObj B] [IsCommMonObj B] {M : CP B}




end Levels

end GlobalTheory.UniformizationSetting
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM

namespace GlobalTheory.SpecialAmple

theorem exists_sec_ne_zero {X X' : Scheme.{0}} (π : X' ⟶ X) [IsIso π] {M : LB X} {M' : LB X'} (hM : M.IsLB)
    (hM' : M'.IsLB) (h : LBIso M' (M.pull π)) (hs : ∃ s : LB.Sec M, ∃ j, s.f j ≠ 0) :
    ∃ s' : LB.Sec M', ∃ j, s'.f j ≠ 0 := by
  obtain ⟨s, j, hj⟩ := hs
  obtain ⟨w, hw⟩ := h
  obtain ⟨⟨s', hs', -⟩, -⟩ := SecPullIso.section_pull X X' π M M' w hM hM' hw s
  refine ⟨s', ?_⟩
  by_contra h
  push Not at h
  refine hj (fn_ext fun x hx => ?_)
  obtain ⟨z, rfl⟩ := π.surjective x
  obtain ⟨k, hz⟩ := exists_chart hM' z
  have e := hs' z j k hx hz
  have e₀ : gs (𝟙 X') z (M'.U k) (s'.f k) = 0 :=
    (congrArg (gs (𝟙 X') z _) (h k)).trans (AmpleCrit.gs_zero' _ z _ hz)
  replace e := e.trans ((congrArg _ e₀).trans (mul_zero _))
  rw [gs_stalkMap π z _ hx] at e
  rw [AmpleCrit.gs_zero' (𝟙 X) (π z) _ hx]
  exact AmpleCrit.injective_stalkMap π z (e.trans (map_zero _).symm)

theorem exists_iso {X Y S T T' : Scheme.{0}} {φ : Y ⟶ X} {a : Y ⟶ T} {b : X ⟶ S} {f : T ⟶ S}
    (h : IsPullback φ a b f) (e : T' ⟶ T) [IsIso e] (g : T' ⟶ S) (he : e ≫ f = g) :
    ∃ u : pullback b g ⟶ Y, IsIso u ∧ u ≫ φ = pullback.fst b g := by
  subst he
  let u : pullback b (e ≫ f) ⟶ Y := h.lift (pullback.fst _ _) (pullback.snd _ _ ≫ e)
    (by rw [Category.assoc]; exact pullback.condition)
  have hu : u ≫ φ = pullback.fst _ _ := h.lift_fst _ _ _
  have H : IsPullback u (pullback.snd b (e ≫ f)) a e :=
    IsPullback.of_right (by rw [hu]; exact IsPullback.of_hasPullback _ _) (h.lift_snd _ _ _) h
  exact ⟨u, H.isIso_fst_of_isIso, hu⟩

theorem exists_sec_pull {X Y Y' : Scheme.{0}} {N : LB X} (hN : N.IsLB) {a : Y ⟶ X} {b : Y' ⟶ X} (u : Y' ⟶ Y)
    [IsIso u] (hu : u ≫ a = b) (hs : ∃ s : LB.Sec (N.pull a), ∃ j, s.f j ≠ 0) :
    ∃ s : LB.Sec (N.pull b), ∃ j, s.f j ≠ 0 :=
  by
  have pull_isLB : ∀ {X Y : Scheme.{0}} {L : LB X}, L.IsLB → (F : Y ⟶ X) → (L.pull F).IsLB :=
    fun hL F => ReciprocityTheory.ChartRestriction.G.Geo.Tor.pull_isLB hL F
  exact exists_sec_ne_zero u (pull_isLB hN a) (pull_isLB hN b)
    (LBIso.chartPull (chartPullSame N _ _ _ u fun _ => hu.symm) (Geo.Tor.chartPullPull _ u u rfl)
      ⟨_, CubePf.idIsoL_isGen (pull_isLB hN a)⟩) hs

theorem lbIso_pw {Y : Scheme.{0}} {A B : LB Y} (h : LBIso A B) (t : ℤ) :
    LBIso (AbLaw.pw A t) (AbLaw.pw B t) := by
  obtain ⟨w, hw⟩ := h
  refine ⟨⟨fun p => w.s p ^ t⟩, fun p q => ?_⟩
  have e := congrArg (· ^ t) (hw p q)
  simp only [mul_zpow, ← map_zpow] at e
  refine e.trans (congrArg₂ (· * ·) ?_ rfl)
  exact (mul_zpow _ _ t).trans (congrArg₂ (· * ·) (map_zpow _ _ t).symm
    ((inv_zpow _ t).trans (congrArg (·⁻¹) (map_zpow _ _ t).symm)))

theorem isIso_spMap {R R' : Type} [CommRing R] [CommRing R'] (e : R ≃+* R') : IsIso (spMap e.toRingHom) :=
  inferInstanceAs (IsIso (Spec.map e.toCommRingCatIso.hom))

theorem exists_sec_pow {K : Type} [Field K] (P : PolAV (Sp K)) :
    ∃ d : ℕ, 1 ≤ d ∧ ∃ s : LB.Sec (AbLaw.pw P.L d), ∃ j, s.f j ≠ 0 := by
  obtain ⟨d, hd, n, a, ha, -⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy _ P.A P.L P.isLB).1 P.ample
  have hy : eSec P.A (IsLocalRing.closedPoint K) ∈ ⨆ i, nonzeroLocus (a i) := by rw [ha]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
  refine ⟨d, hd, a i, j, fun e => ?_⟩
  rw [e, Scheme.basicOpen_zero] at hj
  exact hj

theorem exists_prime (Ω : Type) [Field Ω] (m : ℕ) (hm : 0 < m) : ∃ n : ℕ, n.Prime ∧ (n : Ω) ≠ 0 ∧ ¬ n ∣ m := by
  obtain ⟨n, hn, hp⟩ := Nat.exists_infinite_primes (m + ringChar Ω + 1)
  refine ⟨n, hp, fun h => ?_, fun h => ?_⟩
  · rcases (Nat.dvd_prime hp).1 ((ringChar.spec Ω n).1 h) with e | e
    · exact CharP.ringChar_ne_one e
    · omega
  · have := Nat.le_of_dvd hm h
    omega

theorem relAmple_special_fibre : Laws → Laws2 → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (P : PolAV (Sp K)) (B : Over (Sp V)) [GrpObj B] [IsCommMonObj B] (M : GlobalTheory.UU.CP B) (φ : P.A.left ⟶ B.left), IsAbelianScheme B → IsGrpPullback P.A B (spMap (algebraMap V K)) φ → LBIso P.L (M.L.L.pull φ) → IsAdicComplete (IsLocalRing.maximalIdeal V) V → RelAmple ((Over.pullback (spMap (IsLocalRing.residue V))).obj B) (M.L.L.pull (pullback.fst B.hom (spMap (IsLocalRing.residue V)))) := by
  intro hL hL2 V K _ _ _ _ _ _ P B _ _ M φ hB hφ hiso hV
  have := hB.smooth
  have := hB.proper
  have := hB.geomConnected
  obtain ⟨d, hd, h₀⟩ := exists_sec_pow P
  have pull_isLB : ∀ {X Y : Scheme.{0}} {L : LB X}, L.IsLB → (F : Y ⟶ X) → (L.pull F).IsLB :=
    fun hL F => ReciprocityTheory.ChartRestriction.G.Geo.Tor.pull_isLB hL F
  set_option backward.isDefEq.respectTransparency false in
  have isLB_pw : ∀ {X : Scheme.{0}} {H : LB X}, H.IsLB → (t : ℤ) → (AbLaw.pw H t).IsLB := by
    intro X H hH t
    refine { cover := hH.cover, g_self := ?_, cocycle := ?_ }
    · intro i
      have h := congrArg (· ^ t) (hH.g_self i)
      simpa only [AbLaw.pw, one_zpow, ← map_zpow] using h
    · intro i j k
      have h := congrArg (· ^ t) (hH.cocycle i j k)
      simpa only [AbLaw.pw, mul_zpow, ← map_zpow] using h
  have hN := isLB_pw M.L.isLB d

  have h₁ : ∃ s : LB.Sec ((AbLaw.pw M.L.L d).pull φ), ∃ j, s.f j ≠ 0 := by
    refine exists_sec_ne_zero (𝟙 _) (isLB_pw P.isLB d) (pull_isLB hN φ) ?_ h₀
    refine LBIso.chartPull (chartPullId _) (Geo.Tor.chartPullPull _ (𝟙 _) (𝟙 _) rfl) ?_
    rw [AmpleCrit.pull_pw_eq]
    exact lbIso_pw hiso.symm d
  have h₂ : ∃ s : LB.Sec ((AbLaw.pw M.L.L d).pull (pullback.fst B.hom (jK V))), ∃ j, s.f j ≠ 0 := by
    let e : K ≃+* FractionRing V := (FractionRing.algEquiv V K).symm.toRingEquiv
    have := isIso_spMap e
    obtain ⟨u, _, hu⟩ := exists_iso hφ.1 (spMap e.toRingHom) (jK V) (by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext v
      exact (FractionRing.algEquiv V K).symm.commutes v)
    exact exists_sec_pull hN u hu h₁

  have h₃ := GlobalTheory.SpreadSec.exists_ne_zero_closed_fibre V B _ hN h₂
  let r := spMap (IsLocalRing.residue V)
  have h₄ : ∃ s : LB.Sec ((AbLaw.pw M.L.L d).pull (pullback.fst B.hom r)), ∃ j, s.f j ≠ 0 := by
    let e : (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) ≃+* IsLocalRing.ResidueField V :=
      Ideal.quotEquivOfEq (by rw [zero_add, pow_one])
    have := isIso_spMap e
    obtain ⟨u, _, hu⟩ := exists_iso
      (IsPullback.of_hasPullback B.hom (thick V (IsLocalRing.maximalIdeal V) 0)) (spMap e.toRingHom) r (by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2)
    exact exists_sec_pull hN u hu h₃
  rw [AmpleCrit.pull_pw_eq] at h₄
  obtain ⟨s, hs⟩ := h₄

  let k := IsLocalRing.ResidueField V
  let B' : Over (Sp k) := (Over.pullback r).obj B
  have h : IsGrpPullback B' B r (pullback.fst B.hom r) := isGrpPullback_pullback B r
  have : IsCommMonObj B' := PolPull.isCommMonObj_of_isGrpPullback h
  have hB' : IsAbelianScheme B' := {
    comm := inferInstance
    smooth := MorphismProperty.of_isPullback (P := @Smooth) h.1 hB.smooth
    proper := MorphismProperty.of_isPullback (P := @IsProper) h.1 hB.proper
    geomConnected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) h.1 hB.geomConnected }
  obtain ⟨hL', hr, ⟨c', -⟩, -⟩ := CubePf.cubePull _ _ B B' (cubeMapOf h) M.L M.c
  let Ω := AlgebraicClosure k
  obtain ⟨n, hn, hnΩ, hnd⟩ := exists_prime Ω (2 * d) (by omega)
  refine AmpleCrit.relAmple_of_effective (GlobalTheory.T.card_torsion_points_abelianVariety hL.globalFns hL.rigidity) k (Field.toIsField k) B' hB'
    ((cubeMapOf h).rigLB M.L hL' hr) c' d s hd hs Ω (spMap (algebraMap k Ω)) n hn hnΩ hnd fun x hxn htr => ?_
  let f : V →+* Ω := (algebraMap k Ω).comp (IsLocalRing.residue V)
  have hf : IsLocalHom f := RingHom.isLocalHom_comp _ _
  have key : ∀ p' : Sp Ω ⟶ Sp V, p' = spMap f →
      ∀ y : Over.mk p' ⟶ B, y ^ n = 1 → AbLaw.Triv (translDiff B M.L.L y) → y = 1 := by
    rintro _ rfl
    exact GlobalTheory.T.torsion_eq_one_of_translDiff_trivial_model hL hL2 V K P B M φ hB hφ hiso hV Ω f hf n hnΩ
  have e : pushHom h _ x = 1 := key _ (Spec.map_comp _ _).symm (pushHom h _ x)
    (by rw [← map_pow, hxn, map_one]) (AmpleCrit.triv_translDiff_push h M.L.isLB x htr)
  have e' := e.trans (map_one (pushHom h (Over.mk (spMap (algebraMap k Ω))))).symm
  exact Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun q => q.left) e') (by rw [Over.w, Over.w]))

end GlobalTheory.SpecialAmple
end
