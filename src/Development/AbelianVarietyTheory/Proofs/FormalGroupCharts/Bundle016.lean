module

public import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLawPf
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans

@[expose] public section

section

noncomputable section
open CategoryTheory AlgebraicGeometry MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
namespace GlobalTheory.JetSer

section Val
variable {A : Type} [CommRing A] {X : Scheme.{0}}

def fnValHom (p : Spec (CommRingCat.of A) ⟶ X) (U : X.Opens) (h : ⊤ ≤ p ⁻¹ᵁ U) : Γ(X, U) →+* A :=
  (p.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom).hom

theorem fnVal_eq_fnValHom (p : Spec (CommRingCat.of A) ⟶ X) (U : X.Opens) (h : ⊤ ≤ p ⁻¹ᵁ U) (f : Γ(X, U)) :
    fnVal p U f = fnValHom p U h f := by
  unfold fnVal
  rw [dite_eq_left h]
  rfl

theorem top_le_preimage_comp {T T' : Scheme.{0}} (r : T' ⟶ T) (p : T ⟶ X) (U : X.Opens) (h : ⊤ ≤ p ⁻¹ᵁ U) :
    ⊤ ≤ (r ≫ p) ⁻¹ᵁ U := fun z _ => by
  have : r z ∈ p ⁻¹ᵁ U := h trivial
  simpa using this

theorem fnVal_specMap {B : Type} [CommRing B] (ψ : A →+* B) (p : Spec (CommRingCat.of A) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ p ⁻¹ᵁ U) (f : Γ(X, U)) :
    fnVal (Spec.map (CommRingCat.ofHom ψ) ≫ p) U f = ψ (fnVal p U f) := by
  have h' := top_le_preimage_comp (Spec.map (CommRingCat.ofHom ψ)) p U h
  rw [fnVal_eq_fnValHom _ _ h', fnVal_eq_fnValHom _ _ h]
  have e : (Spec.map (CommRingCat.ofHom ψ) ≫ p).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom =
      (p.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom) ≫ CommRingCat.ofHom ψ := by
    rw [Category.assoc, ← Scheme.ΓSpecIso_naturality, ← Category.assoc,
      ← Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom ψ)) p U ⊤ ⊤ h le_top]
    congr 2
  unfold fnValHom
  rw [e]
  rfl

theorem fnVal_comp {Y : Scheme.{0}} (p : Spec (CommRingCat.of A) ⟶ X) (q : X ⟶ Y) (U : X.Opens) (V : Y.Opens)
    (hUV : U ≤ q ⁻¹ᵁ V) (h : ⊤ ≤ p ⁻¹ᵁ U) (f : Γ(Y, V)) :
    ⊤ ≤ (p ≫ q) ⁻¹ᵁ V ∧ fnVal (p ≫ q) V f = fnVal p U ((q.appLE V U hUV).hom f) := by
  have h' : ⊤ ≤ (p ≫ q) ⁻¹ᵁ V := fun z _ => by
    have : p z ∈ q ⁻¹ᵁ V := hUV (h trivial)
    simpa using this
  refine ⟨h', ?_⟩
  rw [fnVal_eq_fnValHom _ _ h', fnVal_eq_fnValHom _ _ h]
  unfold fnValHom
  rw [← Scheme.Hom.appLE_comp_appLE p q V U ⊤ hUV h]
  rfl

theorem fnVal_res (p : Spec (CommRingCat.of A) ⟶ X) (U V : X.Opens) (hUV : U ≤ V) (h : ⊤ ≤ p ⁻¹ᵁ U)
    (f : Γ(X, V)) :
    ⊤ ≤ p ⁻¹ᵁ V ∧ fnVal p V f = fnVal p U ((X.presheaf.map (homOfLE hUV).op).hom f) := by
  have h' : ⊤ ≤ p ⁻¹ᵁ V := fun z _ => hUV (h trivial)
  refine ⟨h', ?_⟩
  rw [fnVal_eq_fnValHom _ _ h', fnVal_eq_fnValHom _ _ h]
  unfold fnValHom
  rw [← Scheme.Hom.map_appLE p h (homOfLE hUV).op]
  rfl

theorem top_le_preimage_of_nil {B : Type} [CommRing B] (q : A →+* B) (hq : Function.Surjective q)
    (hn : ∀ a ∈ RingHom.ker q, IsNilpotent a) (p : Spec (CommRingCat.of A) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ (Spec.map (CommRingCat.ofHom q) ≫ p) ⁻¹ᵁ U) : ⊤ ≤ p ⁻¹ᵁ U := by
  intro z _
  have hker : RingHom.ker q ≤ z.asIdeal := fun a ha => by
    obtain ⟨n, hn⟩ := hn a ha
    exact z.isPrime.mem_of_pow_mem n (by rw [hn]; exact zero_mem _)
  have := z.isPrime
  have hprime : (z.asIdeal.map q).IsPrime := Ideal.map_isPrime_of_surjective hq hker
  let z₀ : ↥(Spec (CommRingCat.of B)) := (⟨z.asIdeal.map q, hprime⟩ : PrimeSpectrum B)
  have hz : (Spec.map (CommRingCat.ofHom q)) z₀ = z := by
    apply PrimeSpectrum.ext
    change Ideal.comap q (Ideal.map q z.asIdeal) = z.asIdeal
    rw [Ideal.comap_map_of_surjective' q hq, sup_eq_left.mpr hker]
  have h0 : z₀ ∈ (Spec.map (CommRingCat.ofHom q) ≫ p) ⁻¹ᵁ U := h trivial
  rw [← hz]
  simpa using h0

end Val

section Jet
variable {R : Type} [CommRing R] {κ : Type}

theorem jetTruncR_surjective (m : ℕ) : Function.Surjective (jetTruncR R κ m) := by
  intro y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨Ideal.Quotient.mk _ a, rfl⟩

theorem isNilpotent_of_mem_ker_jetTruncR (m : ℕ) (a : JetR R κ (m + 1))
    (ha : a ∈ RingHom.ker (jetTruncR R κ m).toRingHom) : IsNilpotent a := by
  have e : (jetAug R κ m).comp (jetTruncR R κ m) = jetAug R κ (m + 1) :=
    jet_ext fun j => (jetAug_zR m j).trans (jetAug_zR (m + 1) j).symm
  have ha' : jetTruncR R κ m a = 0 := ha
  have h1 : a ∈ RingHom.ker (jetAug R κ (m + 1)) := by
    rw [RingHom.mem_ker, ← e, AlgHom.comp_apply, ha', map_zero]
  refine ⟨m + 1 + 1, ?_⟩
  have := Ideal.pow_mem_pow h1 (m + 1 + 1)
  rwa [ker_jetAug_pow, Ideal.mem_bot] at this

theorem top_le_preimage_jet {X : Scheme.{0}} (p : ∀ m : ℕ, Spec (CommRingCat.of (JetR R κ m)) ⟶ X)
    (hp : ∀ m, (spMap (jetTruncR R κ m)).left ≫ p (m + 1) = p m) (U : X.Opens) (h : ⊤ ≤ p 0 ⁻¹ᵁ U) (m : ℕ) :
    ⊤ ≤ p m ⁻¹ᵁ U := by
  induction m with
  | zero => exact h
  | succ m ih =>
    rw [← hp m] at ih
    exact top_le_preimage_of_nil (jetTruncR R κ m).toRingHom (jetTruncR_surjective m)
      (isNilpotent_of_mem_ker_jetTruncR m) _ U ih

end Jet

theorem serSt_of_jetAlgSt : JetAlgSt → SerSt := by
  intro hJ R _ κ _ X p hp U h0
  have hU := top_le_preimage_jet p hp U h0
  obtain ⟨hτ, -, hinj, hex, -⟩ := hJ R κ
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hc : ∀ f : Γ(X, U), ∃ g : MvPowerSeries κ R, ∀ m, toJet m g = fnValHom (p m) U (hU m) f := by
      intro f
      refine hex (fun m => fnValHom (p m) U (hU m) f) fun m => ?_
      have := fnVal_specMap (jetTruncR R κ m).toRingHom (p (m + 1)) U (hU _) f
      rw [← spMap_left, hp m, fnVal_eq_fnValHom _ _ (hU _), fnVal_eq_fnValHom _ _ (hU _)] at this
      exact this.symm
    choose T hT using hc
    choose τ hτ₁ hτ₂ using hτ
    refine ⟨{ toFun := T
              map_one' := hinj _ _ fun m => by rw [hT, ← hτ₁, map_one, map_one]
              map_mul' := fun a b => hinj _ _ fun m => by
                rw [hT, ← hτ₁, map_mul, map_mul, hτ₁, hτ₁, hT, hT]
              map_zero' := hinj _ _ fun m => by rw [hT, ← hτ₁, map_zero, map_zero]
              map_add' := fun a b => hinj _ _ fun m => by
                rw [hT, ← hτ₁, map_add (f := _), map_add (f := _), hτ₁, hτ₁, hT, hT] }, fun f g => ⟨fun H => ?_, fun H m => ?_⟩⟩
    · exact hinj _ _ fun m => by
        rw [← (H m).2, fnVal_eq_fnValHom _ _ (hU m)]
        exact (hT f m).symm
    · refine ⟨hU m, ?_⟩
      rw [H, fnVal_eq_fnValHom _ _ (hU m)]
      exact (hT f m).symm
  · intro V h f g
    refine forall_congr' fun m => ?_
    obtain ⟨h1, h2⟩ := fnVal_res (p m) U V h (hU m) f
    rw [h2]
    exact ⟨fun H => ⟨hU m, H.2⟩, fun H => ⟨h1, H.2⟩⟩
  · intro Y q V h f g
    refine forall_congr' fun m => ?_
    obtain ⟨h1, h2⟩ := fnVal_comp (p m) q U V h (hU m) f
    rw [h2]
    exact ⟨fun H => ⟨hU m, H.2⟩, fun H => ⟨h1, H.2⟩⟩
  · intro κ' _ b ψ hb hψ f g H m
    refine ⟨top_le_preimage_comp _ _ U (hU m), ?_⟩
    have := fnVal_specMap (ψ m).toRingHom (p m) U (hU m) f
    rw [(H m).2] at this
    exact this.trans (((hJ R κ').2.2.2.2 κ b hb m).2 (ψ m) (hψ m) g)

end GlobalTheory.JetSer
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.TB GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GermExist

theorem isUnit_of_isSer1 (hrep : RepSt) (hser : SerSt) {R : Type} [CommRing R]
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {d : ℕ} {x : Fam G (Fin d)} (hx : IsUnivChart G d x)
    {U : G.left.Opens} {f : Γ(G.left, U)} (hf : IsUnit f) {r : PS R 1 d} (h : IsSer1 x U f r) : IsUnit r := by
  obtain ⟨h1, -, h3, -⟩ := hrep R G d x hx (Fin 1 × Fin d)
  obtain ⟨y, hy, -⟩ := h1 (pt R (n := 1) d 0) (gp_pt 0)
  have hc := (h3 _ y hy).1
  have hs := h 1 _ y hy
  have e : ev (n := 1) ![pt R (n := 1) d 0] r = r := by
    have : (![pt R d 0] : Fin 1 → Pt R 1 d) = fun j => pt R d j := by
      funext j; fin_cases j; rfl
    rw [this]
    unfold ev
    exact congrFun MvPowerSeries.subst_self r
  rw [e] at hs
  obtain ⟨⟨τ, hτ⟩, -⟩ := hser R (Fin 1 × Fin d) G.left (fun m => (y m).left)
    (fun m => by rw [← Over.comp_left, hc m]) U (hs 0).1
  rw [(hτ f r).1 hs]
  exact hf.map τ

theorem top_le_preimage_wchart {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (j : L.ι) (e : Z ⟶ Y) (h : ∀ k, ⊤ ≤ (e ≫ φ k) ⁻¹ᵁ L.U j) : ⊤ ≤ e ⁻¹ᵁ LB.wchart L φ (fun _ => j) := by
  intro z hz
  exact Set.mem_iInter.2 fun k => h k hz

theorem unit_comp_primφ {S : Scheme.{0}} {A : Over S} [GrpObj A] (w : A ⟶ A) (hw : η[A] ≫ w = η[A])
    (k : Fin 5) : η[A].left ≫ primφ w k = η[A].left := by
  have h1 : η[A] ≫ (1 : A ⟶ A) = η[A] := by
    rw [MonObj.comp_one, Hom.one_def]
    simp
  have h2 : η[A] ≫ (𝟙 A * w : A ⟶ A) = η[A] := by
    rw [MonObj.comp_mul, hw, Category.comp_id]
    have : η[A] = (1 : 𝟙_ (Over S) ⟶ A) := by
      rw [Hom.one_def]; simp
    rw [this, _root_.mul_one]
  fin_cases k
  · exact Category.comp_id _
  · exact congrArg (·.left) h2
  · exact Category.comp_id _
  · exact congrArg (·.left) hw
  · exact congrArg (·.left) h1

theorem germ_exists_unique : JetAlgSt → RepSt → SerSt → SerExSt → GermExSt := by
  intro _ hrep hser hex R _ G _ L _ w hw ρ d x hx j hj m s
  obtain ⟨h1, -⟩ := hex R G d x hx
  obtain ⟨σ, hσ, uσ⟩ := h1 (LB.wchart L (K := PUnit) (fun _ => 𝟙 G.left) (fun _ => j))
    (top_le_preimage_wchart L _ j _ (fun _ => by rw [Category.comp_id]; exact hj)) (s.f (fun _ => j))
  obtain ⟨r, hr, ur⟩ := h1 (LB.wchart L (primφ w) (fun _ => j))
    (top_le_preimage_wchart L _ j _ (fun k => by rw [unit_comp_primφ w hw k]; exact hj)) (ρ.s (fun _ => j)).val
  have hu : IsUnit (r ^ m) := (isUnit_of_isSer1 hrep hser hx (Units.isUnit _) hr).pow m
  obtain ⟨v, hv⟩ := hu
  refine ⟨σ * (v⁻¹).val, ⟨σ, r, hσ, hr, by rw [← hv, Units.inv_mul_cancel_right]⟩, ?_⟩
  rintro f ⟨σ', r', hσ', hr', hf⟩
  rw [uσ σ' hσ', ur r' hr', ← hv] at hf
  rw [← hf, Units.mul_inv_cancel_right]

end GlobalTheory.GermExist
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.JetSer

theorem IsFPt.zero_eq_one {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {κ : Type}
    {y : Fam G κ} (hy : IsFPt y) : y 0 = 1 := by
  have hc : (Algebra.ofId R (JetR R κ 0)).comp (jetAug R κ 0) = AlgHom.id R _ := by
    apply jet_ext
    intro j
    rw [AlgHom.comp_apply, jetAug_zR, map_zero]
    apply jetAug_zero_injective κ
    rw [map_zero, AlgHom.id_apply, jetAug_zR]
  have hid : spMap (R₀ := R) (AlgHom.id R (JetR R κ 0)) = 𝟙 _ := by
    apply Over.OverMorphism.ext
    rw [spMap_left]
    exact Spec.map_id _
  calc y 0 = spMap (R₀ := R) (AlgHom.id R (JetR R κ 0)) ≫ y 0 := by rw [hid, Category.id_comp]
    _ = spMap (Algebra.ofId R (JetR R κ 0)) ≫ spMap (jetAug R κ 0) ≫ y 0 := by
      rw [← Category.assoc, spMap_comp, hc]
    _ = 1 := by rw [hy.2 0]; exact MonObj.comp_one _

theorem exUnique_ser (hJ : JetAlgSt) (hR : RepSt) (hS : SerSt) {R : Type} [CommRing R]
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {d : ℕ} {x : Fam G (Fin d)} (hx : IsUnivChart G d x)
    {k : ℕ} {Y : Over (Spec (CommRingCat.of R))}
    (L : ∀ T : Over (Spec (CommRingCat.of R)), (Fin k → (T ⟶ G)) → (T ⟶ Y))
    (hL : ∀ (T T' : Over (Spec (CommRingCat.of R))) (h : T' ⟶ T) (y : Fin k → (T ⟶ G)),
      h ≫ L T y = L T' (fun j => h ≫ y j))
    (U : Y.left.Opens) (hU : ⊤ ≤ (L _ (fun _ => η[G])).left ⁻¹ᵁ U) (f : Γ(Y.left, U)) :
    ∃! g : PS R k d, ∀ (n : ℕ) (a : Fin k → Pt R n d) (y : Fin k → Fam G (Fin n × Fin d)),
      (∀ j, Rep x (a j) (y j)) → HasSer (fun m => (L _ (fun j => y j m)).left) U f (ev a g) := by
  obtain ⟨h1, -, h3, -, h5⟩ := hR R G d x hx (Fin k × Fin d)
  have hpt : ∀ (j : Fin k) (i : Fin d), constantCoeff (pt R (n := k) d j i) = 0 :=
    fun j => ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gp_pt j
  choose y₀ hy₀ using fun j : Fin k => (h1 (pt R (n := k) d j) (hpt j)).exists
  have hF : ∀ j, IsFPt (y₀ j) := fun j => h3 _ _ (hy₀ j)
  have hcomp : ∀ m, (spMap (jetTruncR R (Fin k × Fin d) m)).left ≫ (L _ (fun j => y₀ j (m + 1))).left =
      (L _ (fun j => y₀ j m)).left := by
    intro m
    rw [← Over.comp_left, hL]
    congr 2
    funext j
    exact (hF j).1 m
  have h0 : ⊤ ≤ (L _ (fun j => y₀ j 0)).left ⁻¹ᵁ U := by
    have e : L _ (fun j => y₀ j 0) = toUnit _ ≫ L _ (fun _ => η[G]) := by
      rw [hL]
      congr 1
      funext j
      exact (hF j).zero_eq_one
    rw [e, Over.comp_left, Scheme.Hom.comp_preimage]
    intro p _
    exact hU (Set.mem_univ _)
  obtain ⟨⟨τ, hτ⟩, -, -, hsub⟩ :=
    hS R (Fin k × Fin d) Y.left (fun m => (L _ (fun j => y₀ j m)).left) hcomp U h0
  refine ⟨τ f, fun n a y hy => ?_, fun g hg => ?_⟩
  · let b : Fin k × Fin d → MvPowerSeries (Fin n × Fin d) R := fun p => a p.1 p.2
    have hb : ∀ p, constantCoeff (b p) = 0 := fun p => (hy p.1).1 p.2
    choose ψ hψ using fun m => ((hJ R (Fin n × Fin d)).2.2.2.2 (Fin k × Fin d) b hb m).1
    have hyy : ∀ j, y j = fun m => spMap (ψ m) ≫ y₀ j m := by
      intro j
      have r := h5 (Fin n × Fin d) b ψ hb hψ _ _ (hy₀ j)
      have e : (fun i => MvPowerSeries.subst b (pt R (n := k) d j i)) = a j := by
        funext i
        exact MvPowerSeries.subst_X (hasSubst_of_constantCoeff_zero hb) (j, i)
      rw [e] at r
      exact ((hR R G d x hx (Fin n × Fin d)).1 (a j) (hy j).1).unique (hy j) r
    have r := hsub (Fin n × Fin d) b ψ hb hψ f (τ f) ((hτ f _).2 rfl)
    have e : (fun m => (L _ (fun j => y j m)).left) =
        fun m => (spMap (ψ m)).left ≫ (L _ (fun j => y₀ j m)).left := by
      funext m
      rw [← Over.comp_left, hL]
      simp only [hyy]
    rw [e]
    exact r
  · have r := hg k (fun j => pt R (n := k) d j) y₀ hy₀
    have e : ev (fun j => pt R (n := k) d j) g = g := by
      unfold ev
      exact congrFun MvPowerSeries.subst_self g
    rw [e] at r
    exact (hτ f g).1 r

theorem serEx : JetAlgSt → RepSt → SerSt → SerExSt := by
  intro hJ hR hS R _ G _ d x hx
  refine ⟨fun U hU f => ?_, fun U hU f => ?_, fun U hU f => ?_⟩
  · have H := exUnique_ser hJ hR hS hx (k := 1) (Y := G) (fun _ y => y 0) (fun _ _ _ _ => rfl) U hU f
    refine (existsUnique_congr fun g => ⟨fun h n a y ha => ?_, fun h n a y ha => ?_⟩).1 H
    · exact h n ![a] ![y] (fun j => by fin_cases j; exact ha)
    · have e : a = ![a 0] := by funext j; fin_cases j; rfl
      rw [e]
      exact h n (a 0) (y 0) (ha 0)
  · have H := exUnique_ser hJ hR hS hx (k := 2) (Y := G ⊗ G) (fun _ y => lift (y 0) (y 1))
      (fun _ _ _ _ => comp_lift _ _ _) U hU f
    refine (existsUnique_congr fun g => ⟨fun h n a b y z ha hb => ?_, fun h n a y ha => ?_⟩).1 H
    · exact h n ![a, b] ![y, z] (fun j => by fin_cases j; exacts [ha, hb])
    · have e : a = ![a 0, a 1] := by funext j; fin_cases j <;> rfl
      rw [e]
      exact h n (a 0) (a 1) (y 0) (y 1) (ha 0) (ha 1)
  · have H := exUnique_ser hJ hR hS hx (k := 3) (Y := G ⊗ G ⊗ G)
      (fun _ y => lift (y 0) (lift (y 1) (y 2)))
      (fun _ _ _ _ => by rw [comp_lift, comp_lift]) U hU f
    refine (existsUnique_congr fun g => ⟨fun h n a b c y z w ha hb hc => ?_, fun h n a y ha => ?_⟩).1 H
    · exact h n ![a, b, c] ![y, z, w] (fun j => by fin_cases j; exacts [ha, hb, hc])
    · have e : a = ![a 0, a 1, a 2] := by funext j; fin_cases j <;> rfl
      rw [e]
      exact h n (a 0) (a 1) (a 2) (y 0) (y 1) (y 2) (ha 0) (ha 1) (ha 2)

end GlobalTheory.JetSer
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.JetSer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.JetMap

theorem isFPt_comp {R : Type} [CommRing R] {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [GrpObj G']
    {κ : Type} {y : Fam G κ} (hy : IsFPt y) (f : G ⟶ G') (hf : η[G] ≫ f = η[G']) :
    IsFPt (fun m => y m ≫ f : Fam G' κ) := by
  refine ⟨fun m => ?_, fun m => ?_⟩
  · show spMap _ ≫ y (m + 1) ≫ f = y m ≫ f
    rw [← Category.assoc, hy.1 m]
  · show spMap _ ≫ y m ≫ f = 1
    rw [← Category.assoc, hy.2 m, Hom.one_def, Hom.one_def, Category.assoc, hf]

theorem mapSt (hJ : JetAlgSt) (hR : RepSt) : MapSt := by
  intro R _ G _ G' _ d x x' hx hx' f hf
  obtain ⟨hex, -, hfp, -, hsub⟩ := hR R G d x hx (Fin 1 × Fin d)
  obtain ⟨-, hco', -, -, hsub'⟩ := hR R G' d x' hx' (Fin 1 × Fin d)
  obtain ⟨y₀, hy₀, -⟩ := hex (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt R (n := 1) d 0) (gp_pt 0)
  obtain ⟨φ, hφ, hu⟩ := hco' _ (isFPt_comp (hfp _ _ hy₀) f hf)
  refine ⟨φ, ⟨hφ.1, fun n a y hy => ?_⟩, fun φ' hφ' => ?_⟩
  · have hb : ∀ p : Fin 1 × Fin d, constantCoeff ((![a] : Fin 1 → Pt R n d) p.1 p.2) = 0 :=
      fun p => single_point_zero_constant (a := a) hy.1 p.1 p.2
    have hψ := fun m => ((hJ R (Fin n × Fin d)).2.2.2.2 (Fin 1 × Fin d) _ hb m).1
    choose ψ hψ using hψ
    have h1 := hsub (Fin n × Fin d) _ ψ hb hψ _ _ hy₀
    have h2 := hsub' (Fin n × Fin d) _ ψ hb hψ _ _ hφ
    have h1' : Rep x a (fun m => spMap (ψ m) ≫ y₀ m) := by
      have := gt_comp1_pt a hy.1
      rw [← this]
      exact h1
    have e : y = fun m => spMap (ψ m) ≫ y₀ m :=
      ((hR R G d x hx (Fin n × Fin d)).1 a hy.1).unique hy h1'
    subst e
    simp only [Category.assoc]
    exact h2
  · have := hφ'.2 1 _ _ hy₀
    rw [gt_comp1_pt_right] at this
    exact hu _ this

theorem toJet_one_eq_sum {R : Type} [CommRing R] {κ : Type} [Fintype κ] (g : MvPowerSeries κ R)
    (hg : constantCoeff g = 0) :
    toJet 1 g = ∑ p, coeff (Finsupp.single p 1) g • zR (R := R) 1 p := by
  classical
  have h : truncTotal (1 + 1) g = ∑ p, coeff (Finsupp.single p 1) g • (MvPolynomial.X p : MvPolynomial κ R) := by
    ext e
    rw [coeff_truncTotal_eq_ite, MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_smul, MvPolynomial.coeff_X', smul_eq_mul, mul_ite, _root_.mul_one, mul_zero]
    by_cases he : ∃ p, Finsupp.single p 1 = e
    · obtain ⟨p, rfl⟩ := he
      rw [if_pos (by simp), Finset.sum_eq_single p (fun q _ hq => if_neg fun h =>
        hq (Finsupp.single_left_injective one_ne_zero h)) (by simp), if_pos rfl]
    · rw [Finset.sum_eq_zero fun p _ => if_neg fun h => he ⟨p, h⟩]
      split_ifs with hd
      · have h0 : e.degree = 0 := by
          by_contra h0
          have h1 : e.degree = 1 := by omega
          have : e ∈ Set.range (fun a : κ => Finsupp.single a 1) := by
            rw [Finsupp.range_single_one]; exact h1
          exact he this
        rw [(Finsupp.degree_eq_zero_iff e).1 h0]
        simpa using hg
      · rfl
  unfold toJet
  rw [h]
  exact (map_sum (Ideal.Quotient.mkₐ R _) _ _).trans
    (Finset.sum_congr rfl fun p _ => map_smul (Ideal.Quotient.mkₐ R _) _ _)

theorem dLinSt (hR : RepSt) : DLinSt := by
  intro R _ G _ G' _ d x x' hx hx' f φ hφ w hw hw'
  obtain ⟨y₀, hy₀, -⟩ := (hR R G d x hx (Fin 1 × Fin d)).1
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt R (n := 1) d 0) (gp_pt 0)
  have h' := hφ.2 1 _ _ hy₀
  rw [gt_comp1_pt_right] at h'
  obtain ⟨ψ₀, hψ₀, e₀⟩ := hy₀.2 1
  obtain ⟨ψ', hψ', e'⟩ := h'.2 1
  set c := tcoord hx w hw with hc
  let l : JetR R (Fin 1 × Fin d) 1 →ₐ[R] DualNumber R :=
    jetLift (R := R) (RingHom.ker (fstD R)) kerD_sq (fun p => TrivSqZeroExt.inr (c p.2)) (fun _ => inr_mem_kerD _)
  have hl : ∀ p, l (zR 1 p) = TrivSqZeroExt.inr (c p.2) := fun p => jetLift_zR _ _ _ _ p
  have e1 : l.comp ψ₀ = dualLift c := jet_ext fun j => by
    rw [AlgHom.comp_apply, hψ₀, dualLift_zR]
    exact (congrArg l (toJet_X 1 _)).trans (hl _)
  have e2 : l.comp ψ' = dualLift ((dLin φ).mulVec c) := jet_ext fun j => by

    rw [AlgHom.comp_apply, hψ', dualLift_zR, toJet_one_eq_sum _ (hφ.1 j), map_sum]
    simp only [map_smul, hl, ← TrivSqZeroExt.inr_smul, smul_eq_mul]
    rw [← TrivSqZeroExt.inr_sum, Fintype.sum_prod_type, Fin.sum_univ_one]
    rfl
  apply tcoord_eq
  have e'' : y₀ 1 ≫ f = spMap ψ' ≫ x' 1 := e'
  rw [← e2, ← spMap_comp, Category.assoc, ← e'', e₀, ← Category.assoc, ← Category.assoc, spMap_comp, e1,
    ← tcoord_spec hx w hw]

theorem mapSt_and_dLinSt : JetAlgSt → RepSt → MapSt ∧ DLinSt :=
  fun hJ hR => ⟨mapSt hJ hR, dLinSt hR⟩

end GlobalTheory.JetMap
end
end
