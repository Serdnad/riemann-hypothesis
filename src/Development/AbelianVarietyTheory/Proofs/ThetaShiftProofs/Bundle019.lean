module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ProdTermAddPeriodTranslationLattice
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueSpecializes
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HasSumLocallyUniformlyOnTerm
import Mathlib.RingTheory.LaurentSeries

@[expose] public section

section

noncomputable section
namespace GlobalTheory.ArcPts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace SecValue

variable {K R : Type} [CommRing K] [CommRing R] {X Z : Scheme.{0}}

theorem res_constFn (p : X ⟶ Sp K) {U V : X.Opens} (h : V ≤ U) (a : K) :
    (X.presheaf.map (homOfLE h).op).hom (constFn p U a) = constFn p V a := by
  exact congrArg (fun q : Γ(Sp K, ⊤) ⟶ Γ(X, V) => q.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a))
    (p.appLE_map (U := ⊤) (V := U) le_top (homOfLE h).op)

theorem valR_constFn (p : X ⟶ Sp K) (f : K →+* R) (q : Sp R ⟶ X) (hq : q ≫ p = spMap f) (U : X.Opens)
    (h : ⊤ ≤ q ⁻¹ᵁ U) (a : K) : valR q U (constFn p U a) = f a := by
  refine (HolHom.valR_appLE q p ⊤ U le_top _ h).trans ?_
  rw [hq, ← Category.comp_id (spMap f),
    HolHom.valR_spMap f (𝟙 _) ⊤ le_rfl, HolHom.valR_eq _ _ le_rfl]
  congr 1
  exact congrArg (fun g : CommRingCat.of K ⟶ CommRingCat.of K => g.hom a)
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv_hom_id

def subComb (p : X ⟶ Sp K) {M : LB X} (s : M.Sec) {n : ℕ} (r : Fin n → K) (σ : Fin n → M.Sec) : M.Sec where
  f j := s.f j - ∑ i, constFn p _ (r i) * (σ i).f j
  compat j k := by

    rw [map_sub, map_sub, map_sum, map_sum, mul_sub, s.compat j k, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, res_constFn, res_constFn, (σ i).compat j k]
    ring

theorem valR_subComb (p : X ⟶ Sp K) {M : LB X} (s : M.Sec) {n : ℕ} (r : Fin n → K) (σ : Fin n → M.Sec)
    (f : K →+* R) (q : Sp R ⟶ X) (hq : q ≫ p = spMap f) (j : M.ι) (h : ⊤ ≤ q ⁻¹ᵁ M.U j) :
    valR q _ ((subComb p s r σ).f j) = valR q _ (s.f j) - ∑ i, f (r i) * valR q _ ((σ i).f j) := by

  simp only [← valR_constFn p f q hq _ h, HolHom.valR_eq _ _ h, subComb, map_sub, map_sum, map_mul]

theorem sval_subComb {L : LB Z} {π : X ⟶ Z} {m : ℕ} (p : X ⟶ Sp K) (s : SecP L π m) {n : ℕ} (r : Fin n → K)
    (σ : Fin n → SecP L π m) (f : K →+* R) (q : Sp R ⟶ X) (hq : q ≫ p = spMap f) (j : L.ι)
    (h : ⊤ ≤ (q ≫ π) ⁻¹ᵁ L.U j) :
    ArcPts.sval (subComb p s r σ : SecP L π m) q j = ArcPts.sval s q j - ∑ i, f (r i) * ArcPts.sval (σ i) q j := by
  have hw : ⊤ ≤ q ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => π) (fun _ => j) :=
    fun z hz => Set.mem_iInter.2 fun _ => h hz
  exact valR_subComb p s r σ f q hq (fun _ => j) hw

theorem sval_eq_zero {L : LB Z} {π : X ⟶ Z} {m : ℕ} (s : SecP L π m) (hs : ∀ i, s.f i = 0) (q : Sp R ⟶ X) (j : L.ι) :
    ArcPts.sval s q j = 0 := by
  refine (congrArg (valR q _) (hs fun _ => j)).trans ?_
  by_cases h : ⊤ ≤ q ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => π) (fun _ => j)
  · exact (HolHom.valR_eq q _ h 0).trans (map_zero _)
  · exact dif_neg h

end SecValue

theorem sval_eq_sum_of_hasVal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (S : Scheme.{0}) (A : AnArc (𝓞 E)) (t : SAB H S) (y : Sp ℂ⸨X⸩ ⟶ S) (Φ : GenPts A t y) (j : ℕ) [NeZero j] (s : SecP t.PP.L (pullback.fst t.G.hom y) j) (n : ℕ) (r : Fin n → ℂ⸨X⸩) (α : Fin n → A.X) (th : Fin n → (Fin A.gB → ℂ) → ℂ), (∀ i, th i ∈ A.Theta j (α i)) → (∀ v, HasVal s (fib (Φ.x v)) (Φ.τ v) (∑ i, r i * A.FSum j (α i) (th i) v)) → ∀ (R : Type) [CommRing R] (f : ℂ⸨X⸩ →+* R) (q : Sp R ⟶ pullback t.G.hom y), q ≫ pullback.snd _ _ = spMap f → ∀ jj, ⊤ ≤ (q ≫ pullback.fst _ _) ⁻¹ᵁ t.PP.L.U jj → sval s q jj = ∑ i, f (r i) * sval (Φ.sig j (α i) (th i)) q jj := by
  intro E _ _ _ H _ S A t y Φ j _ s n r α th hth hs R _ f q hq jj hjj
  have h0 := Φ.sep j (SecValue.subComb (pullback.snd t.G.hom y) s r fun i => Φ.sig j (α i) (th i)) fun v k hk => by
    have hv : fib (Φ.x v) ≫ pullback.snd t.G.hom y = spMap (RingHom.id _) := by
      rw [fib, pullback.lift_snd]
      exact (Spec.map_id _).symm
    rw [SecValue.sval_subComb _ s r _ _ _ hv k hk, hs v k hk, Finset.sum_mul, zero_mul, sub_eq_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Φ.val j (α i) (th i) (hth i) v k hk, RingHom.id_apply, _root_.mul_assoc]
  have h1 := SecValue.sval_eq_zero _ h0 q jj
  rwa [SecValue.sval_subComb _ s r _ f q hq jj hjj, sub_eq_zero] at h1

end GlobalTheory.ArcPts
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.SpecGroup

section General

variable {S : Scheme.{0}} {G T T' : Over S}

theorem left_mul_of_comp [GrpObj G] (r : T'.left ⟶ T.left) (hr : r ≫ T.hom = T'.hom) {a b : T ⟶ G} {a' b' : T' ⟶ G}
    (ha : a'.left = r ≫ a.left) (hb : b'.left = r ≫ b.left) : (a' * b').left = r ≫ (a * b).left := by
  have e₁ : a' = Over.homMk r hr ≫ a := Over.OverMorphism.ext ha
  have e₂ : b' = Over.homMk r hr ≫ b := Over.OverMorphism.ext hb
  rw [e₁, e₂, ← MonObj.comp_mul]
  rfl

theorem left_one [GrpObj G] : (1 : T ⟶ G).left = T.hom ≫ eSec G := by
  rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
  rfl

theorem map_zero_eq_one {V M : Type} [AddGroup V] [Group M] (x : V → M) (h : ∀ v v', x (v + v') = x v * x v') :
    x 0 = 1 := by
  have := h 0 0
  rw [add_zero] at this
  exact left_eq_mul.1 this

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem ext_of_generic {A K : Type} [CommRing A] [Field K] {j : A →+* K} (hj : Function.Injective j)
    [IsSeparated G.hom] {p : Sp A ⟶ S} {a b : Over.mk p ⟶ G} (h : spMap j ≫ a.left = spMap j ≫ b.left) : a = b := by
  have : IsDominant (spMap j) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical j).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot j).1 hj]; exact bot_le)⟩
  have : IsDomain A := hj.isDomain j
  exact Over.OverMorphism.ext
    (ext_of_isDominant_of_isSeparated (X := Sp A) G.hom ((Over.w a).trans (Over.w b).symm) (spMap j) h)

theorem le_preimage_of_unit {A K : Type} [CommRing A] [Field K] (ρ : A →+* K) (hρ : ∀ s, ρ s ≠ 0 → IsUnit s)
    {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ (spMap ρ ≫ x) ⁻¹ᵁ U) : ⊤ ≤ x ⁻¹ᵁ U := by
  intro p _
  have h₀ : spMap ρ (⊥ : PrimeSpectrum K) ∈ x ⁻¹ᵁ U := h (x := (⊥ : PrimeSpectrum K)) trivial
  have hs : (show PrimeSpectrum A from p) ⤳ (show PrimeSpectrum A from spMap ρ (⊥ : PrimeSpectrum K)) := by
    refine (PrimeSpectrum.le_iff_specializes _ _).1 fun s hs => ?_
    change ρ s ∈ (⊥ : Ideal K)
    rw [Ideal.mem_bot]
    by_contra hne
    exact (show PrimeSpectrum A from p).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hs (hρ s hne))
  exact hs.mem_open (x ⁻¹ᵁ U).isOpen h₀

theorem isFrm_map {A K : Type} [CommRing A] [Field K] (ρ : A →+* K) (hρ : ∀ s, ρ s ≠ 0 → IsUnit s)
    {X : Scheme.{0}} (L : LB X) (x : Sp A ⟶ X) (τ : L.ι → A) (h : IsFrm L x τ) :
    IsFrm L (spMap ρ ≫ x) (fun j => ρ (τ j)) := by
  refine ⟨fun j hj => (h.1 j (le_preimage_of_unit ρ hρ x _ hj)).map ρ, fun j j' hj => ?_⟩
  have hx := le_preimage_of_unit ρ hρ x _ hj
  rw [HolHom.valR_spMap ρ x _ hx, ← map_mul, ← h.2 j j' hx]

end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)] {S : Scheme.{0}}
  {A : AnArc (𝓞 E)} {t : SAB H S} {y : Sp ℂ⸨X⸩ ⟶ S} {Φ : GenPts A t y} {Γ : Germs} (Ψ : SpecPts Φ Γ)
  {w : ℂ} (hw : Ψ.T < w.im)

theorem val_base :
    spMap (Γ.R w).val.toRingHom ≫ spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom ≫ Ψ.yT = y := by
  rw [← Category.assoc, spMap_comp_spMap]
  exact Ψ.yT_gen

theorem ev_base :
    spMap (Γ.ev w).toRingHom ≫ spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom ≫ Ψ.yT = Ψ.yw w := by
  rw [← Category.assoc, spMap_comp_spMap, Ψ.yw_eq w hw]
  congr 2
  exact RingHom.ext fun s => Γ.ev_eq Ψ.T w hw s

theorem xt_add (v v' : A.V) : Ψ.xt w hw (v + v') = Ψ.xt w hw v * Ψ.xt w hw v' := by
  have := t.semi.separated
  refine ext_of_generic (j := (Γ.R w).val.toRingHom) Subtype.val_injective ?_
  rw [Ψ.xt_gen, Φ.add]
  exact left_mul_of_comp (T' := Over.mk y) _ (val_base Ψ hw) (Ψ.xt_gen w hw v).symm (Ψ.xt_gen w hw v').symm

theorem xt_act (e : 𝓞 E) (v : A.V) : Ψ.xt w hw (A.actV e v) = Ψ.xt w hw v ≫ t.act.act e := by
  have := t.semi.separated
  refine ext_of_generic (j := (Γ.R w).val.toRingHom) Subtype.val_injective ?_
  rw [Ψ.xt_gen, Φ.lin, Over.comp_left, Over.comp_left, ← Ψ.xt_gen w hw v, Category.assoc]

include hw

theorem pi_add (v v' : A.V) : Ψ.pi w (v + v') = Ψ.pi w v * Ψ.pi w v' := by
  refine Over.OverMorphism.ext ?_
  rw [Ψ.pi_eq w hw, xt_add]
  exact (left_mul_of_comp (T' := Over.mk (Ψ.yw w)) _ (ev_base Ψ hw) (Ψ.pi_eq w hw v) (Ψ.pi_eq w hw v')).symm

theorem pi_act (e : 𝓞 E) (v : A.V) : Ψ.pi w (A.actV e v) = Ψ.pi w v ≫ t.act.act e := by
  refine Over.OverMorphism.ext ?_
  rw [Ψ.pi_eq w hw, xt_act, Over.comp_left, Over.comp_left, Ψ.pi_eq w hw, Category.assoc]

theorem pi_frm (v : A.V) : IsFrm t.PP.L (Ψ.pi w v).left (fun j => Ψ.fr w j v) := by
  rw [Ψ.pi_eq w hw]
  exact isFrm_map (Γ.ev w).toRingHom (Γ.unit w) _ _ _ (Ψ.τt_frm w hw v)

theorem pi_rig (j : t.PP.L.ι) (hj : ⊤ ≤ (Ψ.pi w 0).left ⁻¹ᵁ t.PP.L.U j) :
    Ψ.fr w j 0 = valAt' (Ψ.yw w) ((t.PP.L.pull (eSec t.G)).U (fun _ => j)) (t.PP.rig.s (fun _ => j)).val := by
  rw [Ψ.pi_eq w hw] at hj
  have h₁ : ⊤ ≤ (Ψ.xt w hw 0).left ⁻¹ᵁ t.PP.L.U j := le_preimage_of_unit (Γ.ev w).toRingHom (Γ.unit w) _ _ hj
  have h₂ : ⊤ ≤ (Φ.x 0).left ⁻¹ᵁ t.PP.L.U j := by
    rw [← Ψ.xt_gen w hw 0]
    exact fun p _ => h₁ (x := spMap (Γ.R w).val.toRingHom p) trivial
  have h₃ : ⊤ ≤ (spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom ≫ Ψ.yT) ⁻¹ᵁ
      (t.PP.L.pull (eSec t.G)).U (fun _ => j) := by
    rw [map_zero_eq_one _ (xt_add Ψ hw), left_one] at h₁
    exact fun p hp => Set.mem_iInter.2 fun _ => h₁ hp
  have h₄ : Ψ.τt w 0 j = valR (spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom ≫ Ψ.yT)
      ((t.PP.L.pull (eSec t.G)).U (fun _ => j)) (t.PP.rig.s (fun _ => j)).val := by
    refine Subtype.ext ?_
    rw [Ψ.τt_gen w hw 0 j h₁, Φ.rig j h₂]
    exact (congrArg (fun q => valR q _ _) (val_base Ψ hw).symm).trans
      (HolHom.valR_spMap (Γ.R w).val.toRingHom _ _ h₃ _)
  rw [SpecPts.fr, h₄, HolHom.valAt'_eq_valR, ← ev_base Ψ hw]
  exact (HolHom.valR_spMap (Γ.ev w).toRingHom _ _ h₃ _).symm

omit hw

theorem specPts_group : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp B) (o : Obj D l bb s) (A : AnArc (𝓞 E)) (y : Sp ℂ⸨X⸩ ⟶ S) (Φ : GenPts A o.t y) (Γ : Germs) (Ψ : SpecPts Φ Γ), ∀ w : ℂ, Ψ.T < w.im → (∀ v v', Ψ.pi w (v + v') = Ψ.pi w v * Ψ.pi w v') ∧ (∀ (e : 𝓞 E) v, Ψ.pi w (A.actV e v) = Ψ.pi w v ≫ o.t.act.act e) ∧ (∀ v, IsFrm o.t.PP.L (Ψ.pi w v).left (fun j => Ψ.fr w j v)) ∧ ∀ j, ⊤ ≤ (Ψ.pi w 0).left ⁻¹ᵁ o.t.PP.L.U j → Ψ.fr w j 0 = valAt' (Ψ.yw w) ((o.t.PP.L.pull (eSec o.t.G)).U (fun _ => j)) (o.t.PP.rig.s (fun _ => j)).val :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ψ _ hw =>
    ⟨pi_add Ψ hw, pi_act Ψ hw, pi_frm Ψ hw, pi_rig Ψ hw⟩

end GlobalTheory.SpecGroup
end
end

section

noncomputable section

namespace GlobalTheory.SpanFrame

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped LaurentSeries PowerSeries

theorem exists_inverse_mem {k K : Type} [Field k] [Field K] [Algebra k K] (F : IntermediateField k K) {ι κ : Type}
    [Fintype ι] [DecidableEq κ] (c : κ → ι → K) (r : ι → κ → K) (hr : ∀ i l, r i l ∈ F)
    (h : ∀ a l, ∑ i, c a i * r i l = if a = l then 1 else 0) :
    ∃ c' : κ → ι → K, (∀ a i, c' a i ∈ F) ∧ ∀ a l, ∑ i, c' a i * r i l = if a = l then 1 else 0 := by
  obtain ⟨π, hπ⟩ := (Algebra.linearMap F K).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 (algebraMap F K).injective)
  have h1 : π 1 = 1 := by simpa using LinearMap.congr_fun hπ 1
  refine ⟨fun a i => π (c a i), fun a i => (π _).2, fun a l => ?_⟩
  have e := congrArg (fun x => (π x : K)) (h a l)
  have e' : ∀ i, π (c a i * r i l) = (⟨r i l, hr i l⟩ : F) * π (c a i) := fun i => by
    rw [mul_comm (c a i)]; exact map_smul π (⟨r i l, hr i l⟩ : F) (c a i)

  simp only [map_sum, e', apply_ite π, h1, map_zero] at e
  rw [IntermediateField.coe_sum] at e
  refine Eq.trans (Finset.sum_congr rfl fun i _ => mul_comm _ _) (e.trans ?_)
  split_ifs <;> rfl

variable {O : Type} [CommRing O] [StarRing O] {A : AnArc O} {N : ℕ} [NeZero N]

theorem IsComb.mono {B B' : Set ℂ⸨X⸩} (h : B ⊆ B') {f : A.V → ℂ⸨X⸩} (hf : IsComb A N B f) : IsComb A N B' f :=
  let ⟨n, r, α, th, h1, h2⟩ := hf
  ⟨n, r, α, th, fun i => ⟨h (h1 i).1, (h1 i).2⟩, h2⟩

theorem exists_no_common_zero (hA : AnFin A) (hN : 2 ≤ N) {n : ℕ} {α : Fin n → A.X}
    {th : Fin n → (Fin A.gB → ℂ) → ℂ} (hth : ∀ i, th i ∈ A.Theta N (α i))
    (hli : LinearIndependent ℂ⸨X⸩ (fun i v => A.FSum N (α i) (th i) v))
    (hsp : ∀ α', ∀ th' ∈ A.Theta N α', ∃ r : Fin n → ℂ⸨X⸩, (∀ i T, r i ∈ Conv.halfRing T) ∧
      ∀ v, A.FSum N α' th' v = ∑ i, r i * A.FSum N (α i) (th i) v)
    {m : ℕ} (f : Fin m → A.V → ℂ⸨X⸩)
    (hf : ∀ i, ∃ T : ℝ, IsComb A N (Conv.halfRing T) (f i) ∧ ∀ v, f i v ∈ Conv.halfRing T)
    (hs : ∀ α', ∀ th' ∈ A.Theta N α', ∃ c : Fin m → ℂ⸨X⸩, ∀ v, A.FSum N α' th' v = ∑ i, c i * f i v) :
    ∃ (T : ℝ) (hm : ∀ i v, f i v ∈ Conv.halfRing T), (∀ i, IsComb A N (Conv.halfRing T) (f i)) ∧
      ∀ (w : ℂ) (hw : T < w.im) v, ∃ i, Conv.ev T w hw ⟨f i v, hm i v⟩ ≠ 0 := by
  classical
  choose T₁ hT₁ hT₁' using hf
  choose ρ hρ hρ' using hsp
  have hR : ∀ i, ∃ R : Fin n → ℂ⸨X⸩, (∀ l, R l ∈ Conv.convLaurent) ∧
      ∀ v, f i v = ∑ l, R l * A.FSum N (α l) (th l) v := fun i => by
    obtain ⟨p, r, β, t, h1, h2⟩ := hT₁ i
    refine ⟨fun l => ∑ a, r a * ρ (β a) (t a) (h1 a).2 l, fun l => sum_mem fun a _ => mul_mem
      (Conv.halfRing_le_convLaurent _ (h1 a).1) (Conv.halfRing_le_convLaurent 0 (hρ _ _ _ l 0)), fun v => ?_⟩
    rw [h2]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hρ' _ _ (h1 a).2 v, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => (mul_assoc _ _ _).symm
  choose R hR hR' using hR
  choose c hc using fun a => hs (α a) (th a) (hth a)
  have key : ∀ (c : Fin m → ℂ⸨X⸩) v, ∑ i, c i * f i v = ∑ l, (∑ i, c i * R i l) * A.FSum N (α l) (th l) v :=
    fun c v => by
      simp only [hR', Finset.mul_sum, Finset.sum_mul, mul_assoc]
      exact Finset.sum_comm
  obtain ⟨c', hc', hc''⟩ := exists_inverse_mem Conv.convLaurent c R hR fun a l =>
    Fintype.linearIndependent_iffₛ.1 hli (fun l => ∑ i, c a i * R i l) (fun l => if a = l then 1 else 0) (by
      funext v
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [← key, ← hc]
      simp) l
  have hF : ∀ a v, A.FSum N (α a) (th a) v = ∑ i, c' a i * f i v := fun a v => by
    rw [key]
    simp [hc'']
  choose T₂ hT₂ using fun a i => Conv.mem_convLaurent_iff_halfRing.1 (hc' a i)
  obtain ⟨T₀, h₀⟩ := A.exists_isConvLine
  obtain ⟨B₁, hB₁⟩ := Finite.exists_le T₁
  obtain ⟨B₂, hB₂⟩ := Finite.exists_le (fun p : Fin n × Fin m => T₂ p.1 p.2)
  have l₀ : T₀ ≤ max T₀ (max B₁ B₂) := le_max_left _ _
  have l₁ : ∀ i, T₁ i ≤ max T₀ (max B₁ B₂) := fun i => (hB₁ i).trans ((le_max_left _ _).trans (le_max_right _ _))
  have l₂ : ∀ a i, T₂ a i ≤ max T₀ (max B₁ B₂) := fun a i =>
    (hB₂ (a, i)).trans ((le_max_right _ _).trans (le_max_right _ _))
  generalize max T₀ (max B₁ B₂) = T at l₀ l₁ l₂
  have hT := h₀.mono l₀
  refine ⟨T, fun i v => Conv.halfRing_mono (l₁ i) (hT₁' i v),
    fun i => IsComb.mono (Conv.halfRing_mono (l₁ i)) (hT₁ i), fun w hw v => ?_⟩
  obtain ⟨t₁, ht₁, ht₁'⟩ := hA.2
  obtain ⟨β, t, ht, hne⟩ := A.exists_Sum_ne_zero_at hT ht₁ ht₁' hw hN v
  by_contra hz
  push Not at hz
  have hm : A.FSum N β t v ∈ Conv.halfRing T := fun _ hw => (AnArc.hasSum_coeff_FSum hT ht hw v).summable
  have e : (⟨_, hm⟩ : Conv.halfRing T) = ∑ a, ⟨_, hρ β t ht a T⟩ * ∑ i,
      (⟨_, Conv.halfRing_mono (l₂ a i) (hT₂ a i)⟩ : Conv.halfRing T) *
        ⟨f i v, Conv.halfRing_mono (l₁ i) (hT₁' i v)⟩ := by
    apply Subtype.ext
    simp only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, ← hF]
    exact hρ' β t ht v
  refine hne ((Conv.ev_eq_of_hasSum hw ⟨_, hm⟩ (AnArc.hasSum_coeff_FSum hT ht hw v)).symm.trans ?_)
  rw [e]

  simp only [map_sum, map_mul, hz, mul_zero, Finset.sum_const_zero]

end GlobalTheory.SpanFrame
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.LiftPoint

open GlobalTheory.Points GlobalTheory.AmpleSpan GlobalTheory.Specialise

section General

variable {A K : Type} [CommRing A] [CommRing K] {j : A →+* K} {X Y : Scheme.{0}} {f : X ⟶ Y} {H : LB X}
  {I : Type} {t : I → LB.Sec H}

theorem exists_lift_of_valR_mem (hj : Function.Injective j) {D : X.Opens} (hD : IsAffineOpen D) (x : Sp K ⟶ X)
    (hx : ⊤ ≤ x ⁻¹ᵁ D) (h : ∀ g, valR x D g ∈ j.range) :
    ∃ ξ : Sp A ⟶ X, ⊤ ≤ ξ ⁻¹ᵁ D ∧ spMap j ≫ ξ = x := by
  choose φ hφ using h
  simp only [valR_eq x D hx] at hφ
  let ψ : Γ(X, D) →+* A := ⟨⟨⟨φ, hj (by simp [hφ])⟩, fun a b => hj (by simp [hφ])⟩, hj (by simp [hφ]),
    fun a b => hj (by simp [hφ])⟩
  refine ⟨_, le_preimage_specMap_fromSpec hD (CommRingCat.ofHom ψ), ?_⟩
  rw [← specMap_valMap_fromSpec hD x hx, ← Category.assoc, ← Spec.map_comp]
  congr 2
  exact CommRingCat.hom_ext (RingHom.ext hφ)

theorem ext_of_spMap_comp [IsAffine Y] (hj : Function.Injective j) {ξ ξ' : Sp A ⟶ Y}
    (h : spMap j ≫ ξ = spMap j ≫ ξ') : ξ = ξ' :=
  ext_of_valR (isAffineOpen_top Y) (le_preimage_top _) (le_preimage_top _) fun g => hj (by
    rw [← valR_spMap_comp j ξ ⊤ (le_preimage_top _), ← valR_spMap_comp j ξ' ⊤ (le_preimage_top _), h])

theorem exists_lift [IsAffine Y] [IsLocalRing A] (ht : EmbedsBy f t) (hj : Function.Injective j) {b : Sp A ⟶ Y}
    {x : Sp K ⟶ X} (hb : x ≫ f = spMap j ≫ b) {c : I → A} (h : HasCoords x t fun l => j (c l)) {m : I}
    (hm : IsUnit (c m)) : ∃ ξ : Sp A ⟶ X, ξ ≫ f = b ∧ spMap j ≫ ξ = x ∧ HasCoords ξ t c := by
  obtain ⟨hD, ρ, hρ, hsurj⟩ := ht.2 m
  have hx := h.le_nonzeroLocus (hm.map j)
  obtain ⟨ξ, hξ, e⟩ := exists_lift_of_valR_mem hj hD x hx fun g => by
    obtain ⟨q, rfl⟩ := hsurj g
    rw [valR_eval₂Hom f x hx]
    induction q using MvPolynomial.induction_on with
    | C a =>
      rw [MvPolynomial.eval₂Hom_C, ← valR_eq, hb, valR_spMap_comp j b ⊤ (le_preimage_top _)]
      exact ⟨_, rfl⟩
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p l hp =>
      rw [map_mul, MvPolynomial.eval₂Hom_X']
      refine mul_mem hp ⟨c l * hm.unit⁻¹.val, (hm.map j).mul_right_cancel ?_⟩
      rw [h.valR_ratio hx (hρ l), ← map_mul, _root_.mul_assoc, IsUnit.val_inv_mul, _root_.mul_one]
  refine ⟨ξ, ext_of_spMap_comp hj ?_, e, ?_⟩
  · rw [← Category.assoc, e, hb]
  · have e' : (fun l => valR ξ (Out.nonzeroLocus (t m)) (ρ l) * c m) = c := funext fun l => hj (by
      rw [map_mul, ← valR_spMap_comp j ξ _ hξ, e]
      exact h.valR_ratio hx (hρ l))
    rw [← e']
    exact (hasCoords_ratio hξ hρ).mul_unit hm

end General

theorem le_preimage_powOver {S : Scheme.{0}} (G : Over S) (L : LB G.left) (U : S.Opens) (N : ℕ) {A : Type}
    [CommRing A] (x : Sp A ⟶ (G.hom ⁻¹ᵁ U).toScheme) {j : L.ι} (h : ⊤ ≤ (x ≫ (G.hom ⁻¹ᵁ U).ι) ⁻¹ᵁ L.U j) :
    ⊤ ≤ x ⁻¹ᵁ (Out.powOver G L U N).U (fun _ => j) :=
  fun _ hz => Set.mem_iInter.2 fun _ => h hz

theorem existsUnique_lift : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsSeparated G.hom] (L : LB G.left) (U : S.Opens) (N n : ℕ) (b : Fin n → LB.Sec (Out.powOver G L U N)) (R K : Type) [CommRing R] [IsLocalRing R] [CommRing K] [IsLocalRing K] (f : R →+* K) (y : Sp R ⟶ S) (x : Sp K ⟶ (G.hom ⁻¹ᵁ U).toScheme) (cf : Fin n → R) (j : L.ι) (u : Kˣ), L.IsLB → IsAffineOpen U → AmpleSpan.EmbedsBy (G.hom ∣_ U) b → Function.Injective f → ⊤ ≤ y ⁻¹ᵁ U → x ≫ (G.hom ⁻¹ᵁ U).ι ≫ G.hom = spMap f ≫ y → ⊤ ≤ (x ≫ (G.hom ⁻¹ᵁ U).ι) ⁻¹ᵁ L.U j → (∀ i, valR x ((Out.powOver G L U N).U (fun _ => j)) ((b i).f (fun _ => j)) = f (cf i) * u) → (∃ i, IsUnit (cf i)) → ∃! x' : Sp R ⟶ (G.hom ⁻¹ᵁ U).toScheme, x' ≫ (G.hom ⁻¹ᵁ U).ι ≫ G.hom = y ∧ spMap f ≫ x' = x ∧ ∀ j', ⊤ ≤ (x' ≫ (G.hom ⁻¹ᵁ U).ι) ⁻¹ᵁ L.U j' → ∃ u' : Rˣ, ∀ i, valR x' ((Out.powOver G L U N).U (fun _ => j')) ((b i).f (fun _ => j')) = cf i * u' := by
  intro S G _ _ L U N n b R K _ _ _ _ f y x cf j u hL hU hb hf hy hxy hj hval ⟨m, hm⟩
  have : IsAffine U := hU
  let y' : Sp R ⟶ U.toScheme := IsOpenImmersion.lift U.ι y (by
    rintro _ ⟨z, rfl⟩
    exact ⟨⟨y z, hy trivial⟩, rfl⟩)
  have ey : y' ≫ U.ι = y := IsOpenImmersion.lift_fac _ _ _
  have key : ∀ ξ : Sp R ⟶ (G.hom ⁻¹ᵁ U).toScheme,
      ξ ≫ (G.hom ⁻¹ᵁ U).ι ≫ G.hom = y ↔ ξ ≫ G.hom ∣_ U = y' := fun ξ => by
    rw [← cancel_mono U.ι, ey, Category.assoc, morphismRestrict_ι]
  have hxy' : x ≫ G.hom ∣_ U = spMap f ≫ y' := by
    rw [← cancel_mono U.ι, Category.assoc, Category.assoc, ey, morphismRestrict_ι, hxy]
  obtain ⟨ξ, h₁, h₂, h₃⟩ := exists_lift hb hf hxy' (c := cf)
    ⟨fun _ => j, le_preimage_powOver G L U N x hj, u, hval⟩ hm
  refine ⟨ξ, ⟨(key ξ).2 h₁, h₂, fun j' hj' => h₃.chart (le_preimage_powOver G L U N ξ hj')⟩, ?_⟩
  rintro ξ' ⟨k₁, -, k₃⟩
  obtain ⟨j', hj'⟩ := exists_le_preimage_of_iSup_eq_top (ξ' ≫ (G.hom ⁻¹ᵁ U).ι) hL.cover
  exact HasCoords.ext hb (((key ξ').1 k₁).trans h₁.symm)
    ⟨fun _ => j', le_preimage_powOver G L U N ξ' hj', k₃ j' hj'⟩ h₃ hm

end GlobalTheory.LiftPoint
end
end
