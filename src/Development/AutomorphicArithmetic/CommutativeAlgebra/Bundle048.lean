module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
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

@[expose] public section

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits
open UpperTheory.Gal.Int.Geo


theorem UpperTheory.tower_finiteEtale_of_trivial_powerCartesian :
    PiZero → PowCart → PiFet := by
  intro h0 hpc p _ D G L E _ _ gb w q _ r 𝔴 𝔫 S k T N c a hN C
  obtain ⟨ρ, e0, hop, hcl, htr⟩ := h0 p D G L E gb w q r 𝔴 𝔫 S k T N c a hN C
  have hx : (1 : G.GAf) ∈ T.X.Δ := T.X.Δ.one_mem
  have hN' : (N : ℕ) = S.N₀ * c := by
    unfold Site.Num at hN
    exact hN.1
  have hsub : ∀ (n m : ℕ) (g : G.GAf), L.CongOne (n * m) g → L.CongOne n g := by
    intro n m g hg
    unfold GlobalTheory.LKGeo.Link.CongOne at hg ⊢
    intro v hv
    obtain ⟨u, hu, huv⟩ := hg v hv
    exact ⟨m • u, AddSubgroup.nsmul_mem _ hu m, by rw [huv, mul_smul]⟩
  obtain ⟨hy, htr'⟩ : ∃ hy, T.X.tr (T.lev N) _ 1 hx hy ≫ ρ = _ := ⟨_, htr hx (by
    intro u hu
    rw [one_mul, inv_one, mul_one]
    rw [T.3] at hu ⊢
    rw [hN'] at hu
    show u ∈ L.KN S.N₀
    unfold GlobalTheory.LKGeo.Link.KN at hu ⊢
    exact ⟨hsub _ _ _ hu.1, hsub _ _ _ hu.2⟩)⟩
  have hG := S.mπ.3
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback at hG
  have hpb := hG.1
  obtain ⟨hP1, hP2, -⟩ := hpc S.Y.X S.M.X S.M.X S.Y.univ.A S.M.univ.A S.M.univ.A S.π (𝟙 _) S.mπ.φ (𝟙 _)
    hpb.w (by simp) k
  have hPB := hP1 hpb
  have hfinP : IsFinite (GlobalTheory.KS.powMap S.π S.mπ.φ hpb.w k) :=
    MorphismProperty.of_isPullback (P := @IsFinite) hPB.flip S.20
  have hetP : Etale (GlobalTheory.KS.powMap S.π S.mπ.φ hpb.w k) :=
    MorphismProperty.of_isPullback (P := @Etale) hPB.flip S.21
  have hcomm : (GlobalTheory.KS.pow S.Y.univ.A k).hom ≫ S.Y.s =
      GlobalTheory.KS.powMap S.π S.mπ.φ hpb.w k ≫ (GlobalTheory.KS.pow S.M.univ.A k).hom ≫ S.M.s := by
    rw [← Category.assoc, hP2, Category.assoc, S.18]
  have eY : S.pi T C ≫ (GlobalTheory.KS.pow S.Y.univ.A k).hom ≫ S.Y.s = T.X.q (T.lev N) ≫ gen (Ow w) E := by
    rw [hcomm, ← Category.assoc, ← htr', Category.assoc, e0, ← Category.assoc, T.X.10]
  refine ⟨eY, ?_⟩
  have h1 : ((GlobalTheory.KS.pow S.Y.univ.A k).hom ≫ S.Y.s) ≫ 𝟙 _ =
      GlobalTheory.KS.powMap S.π S.mπ.φ hpb.w k ≫ (GlobalTheory.KS.pow S.M.univ.A k).hom ≫ S.M.s := by
    rw [Category.comp_id, hcomm]
  have h2 : gen (Ow w) E ≫ 𝟙 _ = 𝟙 _ ≫ gen (Ow w) E := by
    rw [Category.comp_id, Category.id_comp]
  let hm := pullback.map ((GlobalTheory.KS.pow S.Y.univ.A k).hom ≫ S.Y.s) (gen (Ow w) E)
    ((GlobalTheory.KS.pow S.M.univ.A k).hom ≫ S.M.s) (gen (Ow w) E)
    (GlobalTheory.KS.powMap S.π S.mπ.φ hpb.w k) (𝟙 _) (𝟙 _) h1 h2
  have h3 : gen (Ow w) E = 𝟙 _ ≫ gen (Ow w) E := (Category.id_comp _).symm
  have hmF : IsFinite hm := MorphismProperty.pullbackMap (P := @IsFinite) hfinP inferInstance hcomm h3
  haveI := hetP
  have hmU : FormallyUnramified hm :=
    MorphismProperty.pullbackMap (P := @FormallyUnramified) inferInstance inferInstance hcomm h3
  have hkey : pullback.lift (S.pi T C) (T.X.q (T.lev N)) eY ≫ hm =
      T.X.tr _ _ 1 hx hy ≫ pullback.lift ρ _ e0 := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.assoc, pullback.lift_fst, htr']
      simp only [hm, pullback.lift_fst_assoc, pullback.map, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, Category.assoc, pullback.lift_snd, T.X.10]
      simp only [hm, pullback.map, pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id]
  haveI := hop
  haveI := hcl
  haveI := T.X.13 _ _ hx hy
  haveI := T.X.14 _ _ hx hy
  have hcomp : IsFinite (pullback.lift (S.pi T C) (T.X.q (T.lev N)) eY ≫ hm) ∧
      Etale (pullback.lift (S.pi T C) (T.X.q (T.lev N)) eY ≫ hm) := by
    rw [hkey]
    exact ⟨inferInstance, inferInstance⟩
  haveI := hcomp.1
  haveI := hcomp.2
  exact ⟨IsFinite.of_comp _ hm, Etale.of_comp _ hm⟩
end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo

private theorem kn_conj {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) {N : ℕ} {k u : G.GAf}
    (hk : k ∈ L.KN 1) (hu : u ∈ L.KN N) : k * u * k⁻¹ ∈ L.KN N := by
  have key : ∀ g : G.GAf, L.CongOne 1 g → L.CongOne 1 g⁻¹ → ∀ x : G.GAf, L.CongOne N x →
      L.CongOne N (g * x * g⁻¹) := by
    intro g hg hg' x hx
    unfold Link.CongOne at hg hg' hx ⊢
    intro v hv
    obtain ⟨w₁, hw₁, h₁⟩ := hg' v hv
    have hv₁ : L.actG g⁻¹ v ∈ LaHat D := by
      rw [h₁, one_smul]
      exact add_mem hv hw₁
    obtain ⟨w₂, hw₂, h₂⟩ := hx _ hv₁
    obtain ⟨w₃, hw₃, h₃⟩ := hg w₂ hw₂
    refine ⟨w₂ + w₃, add_mem hw₂ hw₃, ?_⟩
    have hgg : L.actG g (L.actG g⁻¹ v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, h₂, map_add (f := _), hgg, map_nsmul, h₃,
      one_smul]
  have hk' : L.CongOne 1 k ∧ L.CongOne 1 k⁻¹ := hk
  have hu' : L.CongOne N u ∧ L.CongOne N u⁻¹ := hu
  show L.CongOne N (k * u * k⁻¹) ∧ L.CongOne N (k * u * k⁻¹)⁻¹
  refine ⟨key k hk'.1 hk'.2 u hu'.1, ?_⟩
  have hinv : (k * u * k⁻¹)⁻¹ = k * u⁻¹ * k⁻¹ := by group
  rw [hinv]
  exact key k hk'.1 hk'.2 u⁻¹ hu'.2

private theorem gen_mono {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    Mono (gen (Ow w) E) := by
  haveI : Epi (CommRingCat.ofHom (algebraMap (Ow w) E)) := IsLocalization.epi (nonZeroDivisors (Ow w)) E
  change Mono (Scheme.Spec.map (CommRingCat.ofHom (algebraMap (Ow w) E)).op)
  infer_instance

theorem UpperTheory.tower_separated_of_trivial_powerCartesian :
    PiZero → BaseSep → PowCart → PiSep := by
  intro hPZ hBS hPC p _ D G L E _ _ gb w q _ r 𝔴 𝔫 S k T K₀ hLev N c a hNum C Ω _ _ z z' hz
  obtain ⟨ρ, e, hopen, -, htr⟩ := hPZ p D G L E gb w q r 𝔴 𝔫 S k T N c a hNum C
  have hKM := T.K_eq ⟨S.N₀, PiZero._proof_1 p D E gb w q r 𝔴 𝔫 S⟩
  revert hKM
  revert ρ
  generalize T.lev ⟨S.N₀, PiZero._proof_1 p D E gb w q r 𝔴 𝔫 S⟩ = M
  intro ρ e hopen htr hKM
  have x : (1 : G.GAf) ∈ T.X.Δ := T.X.Δ.one_mem
  have y : ∀ u ∈ T.X.K (T.lev N), 1 * u * 1⁻¹ ∈ T.X.K M := fun u hu => by
    have hN : S.N₀ ∣ (N : ℕ) := ⟨c, hNum.1⟩
    have hu' : u ∈ L.KN S.N₀ := KN_anti hN (by rw [← T.K_eq]; exact hu)
    rw [hKM]
    simpa using hu'
  have htr' := htr x y
  have hzM : z ≫ T.X.tr (T.lev N) M 1 x y ≫ ρ = z' ≫ T.X.tr (T.lev N) M 1 x y ≫ ρ := by
    rw [htr', ← Category.assoc, hz, Category.assoc]
  have hzq : z ≫ T.X.tr (T.lev N) M 1 x y ≫ T.X.q M = z' ≫ T.X.tr (T.lev N) M 1 x y ≫ T.X.q M := by
    haveI : Mono (gen (Ow w) E) := gen_mono w
    rw [← cancel_mono (gen (Ow w) E)]
    simp only [Category.assoc]
    rw [← e]
    simp only [← Category.assoc] at hzM ⊢
    rw [hzM]
  have hzt : z ≫ T.X.tr (T.lev N) M 1 x y = z' ≫ T.X.tr (T.lev N) M 1 x y := by
    haveI := hopen
    rw [← cancel_mono (pullback.lift ρ (T.X.q M) e)]
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
      exact hzM
    · simp only [Category.assoc, pullback.lift_snd]
      exact hzq
  have hnorm : ∀ g ∈ T.X.K M, ∀ u ∈ T.X.K (T.lev N), g * u * g⁻¹ ∈ T.X.K (T.lev N) := by
    intro g hg u hu
    rw [hKM] at hg
    rw [T.K_eq] at hu ⊢
    exact kn_conj L (KN_anti (one_dvd _) hg) hu
  obtain ⟨g, hg, a', b', hz'⟩ := T.X.trans (T.lev N) M x y hnorm Ω z z' hzt
  refine ⟨g, ?_, a', b', hz'⟩
  rw [hKM] at hg
  obtain ⟨π, o, ψ, φ, hw, hπ, htrans, heq⟩ := T.tr_eq N N g a' b'
  have hP2 := (hPC _ _ _ (T.M N).univ.A (T.M N).univ.A (T.M N).univ.A π (𝟙 _) (Over.Hom.left ψ ≫ φ.φ)
    (𝟙 _) hw (by simp) k).2.1
  have hP3 : Cls.pw C k ≫ (GlobalTheory.KS.pow S.Y.univ.A k).hom = (GlobalTheory.KS.pow (T.M N).univ.A k).hom ≫ C.j :=
    (hPC _ _ _ (T.M N).univ.A S.Y.univ.A S.Y.univ.A C.j (𝟙 _) C.m.φ (𝟙 _) _ (by simp) k).2.1
  have h1 : z' ≫ (T.e N).hom ≫ (GlobalTheory.KS.pow (T.M N).univ.A k).hom =
      z ≫ (T.e N).hom ≫ (GlobalTheory.KS.pow (T.M N).univ.A k).hom ≫ π := by
    rw [hz', Category.assoc, reassoc_of% heq, hP2]
  have h2 : z ≫ (T.e N).hom ≫ (GlobalTheory.KS.pow (T.M N).univ.A k).hom ≫ C.j =
      z' ≫ (T.e N).hom ≫ (GlobalTheory.KS.pow (T.M N).univ.A k).hom ≫ C.j := by
    have hz2 := hz
    unfold Site.pi at hz2
    rw [← hP3]
    simp only [← Category.assoc] at hz2 ⊢
    rw [hz2]
  refine hBS p D G L E gb w q r 𝔴 𝔫 S k T K₀ hLev N c a hNum C g hg ⟨π, o, ψ, φ, hπ, htrans⟩ Ω
    (z ≫ (T.e N).hom ≫ (GlobalTheory.KS.pow (T.M N).univ.A k).hom) ?_
  show (z ≫ (T.e N).hom ≫ (GlobalTheory.KS.pow (T.M N).univ.A k).hom) ≫ π ≫ C.j =
    (z ≫ (T.e N).hom ≫ (GlobalTheory.KS.pow (T.M N).univ.A k).hom) ≫ C.j
  simp only [Category.assoc]
  rw [h2, reassoc_of% h1]
end

section

set_option autoImplicit false

noncomputable section

open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo
open scoped TensorProduct

namespace UpperTheory.Gal.Int.Geo

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G)

private theorem actOn_comm_mulF (x : 𝓞 D.F) (y : AfP p ⊗[ℚ] G.C) :
    actOn L.rep (AfP p) y * mulF D x = mulF D x * actOn L.rep (AfP p) y := by
  induction y using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add (f := _), add_mul, mul_add, ha, hb]
  | tmul a c =>
    have hc : L.rep c * actQ D (algebraMap (𝓞 D.F) D.O x) = actQ D (algebraMap (𝓞 D.F) D.O x) * L.rep c :=
      (L.rep_range (L.rep c)).1 ⟨c, rfl⟩ _
    have hb : (Module.End.baseChangeHom ℚ (AfP p) (VQ D) (L.rep c)) * mulF D x =
        mulF D x * (Module.End.baseChangeHom ℚ (AfP p) (VQ D) (L.rep c)) := by
      have := congrArg (Module.End.baseChangeHom ℚ (AfP p) (VQ D)) hc
      rw [map_mul, map_mul] at this
      exact this
    have ht : actOn L.rep (AfP p) (a ⊗ₜ[ℚ] c) = algebraMap (AfP p) (Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)) a *
        Module.End.baseChangeHom ℚ (AfP p) (VQ D) (L.rep c) :=
      Algebra.TensorProduct.lift_tmul _ _ _ a c
    rw [ht, mul_assoc, hb, ← mul_assoc, ← mul_assoc, Algebra.commutes]

private theorem actG_mulF (g : G.GAf) (x : 𝓞 D.F) (v : AfP p ⊗[ℚ] VQ D) :
    L.actG g (mulF D x v) = mulF D x (L.actG g v) :=
  congrArg (fun f : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D) => f v) (actOn_comm_mulF L x _)

private theorem actG_idHat {g : G.GAf} (hg : Integ L g) (𝔟 : Ideal (𝓞 D.F)) {z : AfP p ⊗[ℚ] VQ D}
    (hz : z ∈ idHat D 𝔟) : L.actG g z ∈ idHat D 𝔟 := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨x, hx, v, hv, rfl⟩ := hz
    rw [actG_mulF]
    exact AddSubgroup.subset_closure ⟨x, hx, _, hg v hv, rfl⟩
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha

end UpperTheory.Gal.Int.Geo

open UpperTheory.Gal.Int.Geo in
theorem UpperTheory.arithmeticGroup_congruenceSubgroupProperty : UpperTheory.Gal.Int.Geo.GrpCong := by
  intro p _ D G L 𝔫 K₀ hK h u _ hc hu hg
  refine (hK _).2 ⟨hg, fun v hv => ?_⟩
  obtain ⟨huK, huC⟩ := (hK u).1 hu
  have huv : L.actG u v ∈ LaHat D := integ_of_mem huK v hv
  have e1 := hc _ huv
  have e2 := huC v hv
  have e3 := actG_idHat L (integ_of_mem hg) 𝔫 (hc v hv)
  have hcomp : L.actG (h * u * h⁻¹) (L.actG h v) = L.actG h (L.actG u v) := by
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    simp
  have key : L.actG (h * u * h⁻¹) v - v = (L.actG h (L.actG u v) - L.actG u v) + (L.actG u v - v)
      - L.actG (h * u * h⁻¹) (L.actG h v - v) := by
    rw [map_sub, hcomp]; abel
  rw [key]
  exact sub_mem (add_mem e1 e2) e3

end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.crystallineComparison.Mod (Std TjD TjE KSOKE)
open UpperTheory.Gal.Int.Geo
open scoped TensorProduct

section SlopeTestRemainingChoices

variable {q : ℕ} [Fact q.Prime] {D : Datum q} {R R' : Type} [CommRing R] [CommRing R'] [Algebra ℚ R'] {b : Base D R}
  {gb : GBase D.toG R'} {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R'} {N N₀ c : ℕ}

private theorem qcast {o' : GObj gb N s'} {o : Obj b N₀ s} {f g : S' ⟶ S} (e : f = g) (n : QMap o' o f c) :
    ∃ n' : QMap o' o g c, n'.φ = n.φ := by
  subst e
  exact ⟨n, rfl⟩

private theorem qobj' (hObj : QObj) (β : R →+* R') (hm : Match b gb β) (hN : N = N₀ * c) (h0 : 0 < N) (hc : N₀.Coprime q)
    (o : GObj gb N s') {s₀ : S' ⟶ Sp R} (e : s₀ = s' ≫ spMap β) : ∃ o₀ : Obj b N₀ s₀, Nonempty (QMap o o₀ (𝟙 S') c) := by
  subst e
  exact hObj q D R R' b gb β hm N N₀ c hN h0 hc S' s' o

private theorem sec_hom {X : Scheme.{0}} {A : Over X} (e : 𝟙_ (Over X) ⟶ A) : e.left ≫ A.hom = 𝟙 X := by
  simpa using Over.w e

private theorem sec_lift {X Y : Scheme.{0}} {A : Over X} {B : Over Y} {f : X ⟶ Y} {φ : A.left ⟶ B.left}
    (hc : IsPullback φ A.hom B.hom f) (e : 𝟙_ (Over Y) ⟶ B) : ∃ l : 𝟙_ (Over X) ⟶ A, l.left ≫ φ = f ≫ e.left := by
  refine ⟨Over.homMk (hc.lift (f ≫ e.left) (𝟙 X) (by simp [sec_hom e])) (by simp), ?_⟩
  simp

end SlopeTestRemainingChoices

theorem UpperTheory.hecke_lift_exists_of_quotient_level :
    NumEx → QObj → QComp → QUniq → QLev → TjIsog → TrEta → CongCRT → LiftEx := by
  intro hNumEx hQObj hQComp hQUniq hQLev hTjIsog hTrEta hCRT p _ D G L E _ _ gb w q _ r 𝔴 𝔫 S k T K₀ hLev i h hi hTj hInt Tj Lj N' N t c a hN't hNum C' C u hu W
  obtain ⟨hNc, hGen⟩ := hNum
  have hN'c : (N' : ℕ) = S.N₀ * (c * t) := by rw [hN't, hNc, _root_.mul_assoc]
  have h3 : 3 ≤ S.N₀ := S.std.three
  have hcq : S.N₀.Coprime q := S.std.cop
  have hNpos : 0 < (N : ℕ) := by have := N.2.1; omega
  have hN'pos : 0 < (N' : ℕ) := by have := N'.2.1; omega
  have e0 : (C'.j ≫ S.π) ≫ S.M.s = (T.M N').s ≫ spMap (algebraMap (Ow w) E) := by
    rw [Category.assoc, S.ov, C'.ov]
  obtain ⟨o₁, ⟨n₁⟩⟩ := qobj' hQObj (algebraMap (Ow w) E) S.mat hN'c hN'pos hcq (T.M N').univ e0
  obtain ⟨o₂, ⟨n₂⟩⟩ := qobj' hQObj (algebraMap (Ow w) E) S.mat hNc hNpos hcq W.o e0
  obtain ⟨ψ₀, hψ₀, hiso, htj⟩ := hTjIsog p D G L E gb w q r 𝔴 𝔫 S k T K₀ hLev i h hTj hInt u hu N' N (c * t) c
    hN'c hNc W _ o₁ o₂ n₁ n₂
  obtain ⟨x1q, hx1q⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ (T.M N').univ S.Y.univ S.M.univ C'.j S.π).1 C'.m S.mπ
  obtain ⟨x1c, hx1c⟩ := qcast (show C'.j ≫ S.π = 𝟙 _ ≫ (C'.j ≫ S.π) by simp) x1q
  obtain ⟨x1, hx1⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ (T.M N').univ o₁ S.M.univ (𝟙 _) (C'.j ≫ S.π)).2.2.1
    inferInstance n₁ x1c
  have hunit : IsUnit ((q : ℕ) : Γ((T.M N').X, ⊤)) := by
    have hqE : IsUnit (q : E) := (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero).isUnit
    simpa using hqE.map (((T.M N').s.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of E)).inv.hom)
  obtain ⟨y₀, ⟨hy₀, m₀, m₁, hm01⟩, -⟩ := Tj.univ _ (C'.j ≫ S.π) o₁ o₂ x1 ψ₀ hunit hiso htj
  obtain ⟨y, hys, hyg⟩ : ∃ y, y ≫ Lj.s = C'.j ∧ y ≫ Lj.g = y₀ :=
    ⟨_, Lj.pb.lift_fst _ _ hy₀.symm, Lj.pb.lift_snd _ _ hy₀.symm⟩
  obtain ⟨n'c, hn'c⟩ := qcast hys.symm C'.m
  obtain ⟨mm, hmm⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ (T.M N').univ Lj.o S.Y.univ y Lj.s).2.1 n'c Lj.ms
  obtain ⟨q1, hq1⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ W.o o₂ Tj.o' (𝟙 _) y₀).1 n₂ m₁
  obtain ⟨q1c, hq1c⟩ := qcast (show 𝟙 _ ≫ y₀ = y ≫ Lj.g by rw [hyg, Category.id_comp]) q1
  obtain ⟨q2, hq2⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ W.o Lj.o' Tj.o' y Lj.g).2.1 q1c Lj.m'
  obtain ⟨q3, hq3⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ W.o Lj.o' S.Y.univ y Lj.t).1 q2 Lj.mt
  obtain ⟨qC, hqC⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ (T.M N).univ S.Y.univ S.Y.univ C.j (𝟙 _)).2.2.2
    _ _ W.o W.π W.φ C.m
  obtain ⟨A1, hA1⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ (T.M N').univ Lj.o Tj.o y Lj.g).1 mm Lj.m₀
  obtain ⟨B1, hB1⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ (T.M N').univ o₁ Tj.o (𝟙 _) y₀).1 n₁ m₀
  obtain ⟨B1c, hB1c⟩ := qcast (show 𝟙 _ ≫ y₀ = y ≫ Lj.g by rw [hyg, Category.id_comp]) B1
  have I1 : mm.φ ≫ Lj.m₀.φ = n₁.φ ≫ m₀.φ := by
    rw [← hA1, ← hB1, ← hB1c]
    exact hQUniq q _ _ _ _ _ _ _ _ h3 hcq _ _ _ _ _ _ _ A1 B1c
  have I2 : mm.φ ≫ Lj.ψ.left = W.ψ.left ≫ q2.φ := by
    apply Lj.m'.cart.1.hom_ext
    · simp only [Category.assoc]
      rw [← Lj.sq, reassoc_of% I1, hm01, reassoc_of% hψ₀, ← hq2, hq1c, hq1]
    · simp only [Category.assoc, Over.w, mm.cart.1.w, q2.cart.1.w]
      rw [← Category.assoc (Over.Hom.left W.ψ), Over.w]
  have hIu : Integ L u := integ_of_mem ((hLev u).mp hu).1
  have hCu : CongId L S.𝔞 u := by
    have h1 := ((hLev u).mp hu).2
    rw [S.lev] at h1
    exact ((hCRT p D G L q r S.N₀ S.𝔞 hcq S.upow u hIu).1.mp h1).2
  have hCh : CongId L S.𝔞 h := hTj.other S.𝔞 S.sup S.upow
  have hx : ∀ y' : D.La, ∃ v ∈ LaHat D, (L.actG (h * u)) (inAf D ((algebraMap (𝓞 D.F) D.O) a • y')) =
      inAf D ((algebraMap (𝓞 D.F) D.O) a • y') + (N : ℕ) • v := by
    intro y'
    obtain ⟨v₁, hv₁, e₁⟩ := ((hCRT p D G L q r S.N₀ S.𝔞 hcq S.upow h hInt).2 a N hNpos N.2.2 hGen).mp hCh y'
    obtain ⟨v₂, hv₂, e₂⟩ := ((hCRT p D G L q r S.N₀ S.𝔞 hcq S.upow u hIu).2 a N hNpos N.2.2 hGen).mp hCu y'
    refine ⟨v₁ + L.actG h v₂, add_mem hv₁ (hInt v₂ hv₂), ?_⟩
    rw [map_mul, Module.End.mul_apply, e₂, map_add (f := _), map_nsmul, e₁, smul_add, add_assoc]
  have I4 : ∀ y' : D.La, ∀ l' : 𝟙_ (Over Lj.Z) ⟶ Lj.o.A, l'.left ≫ Lj.ms.φ = Lj.s ≫ (S.Y.lv y').left →
      ((T.M N').univ.eta (t • ((algebraMap (𝓞 D.F) D.O) a • y'))).left ≫ mm.φ = y ≫ l'.left := by
    intro y' l' hl'
    have hsm : (algebraMap (𝓞 D.F) D.O (↑t * a)) • y' = t • ((algebraMap (𝓞 D.F) D.O) a • y') := by
      rw [map_mul, map_natCast, mul_smul, Nat.cast_smul_eq_nsmul]
    apply Lj.ms.cart.1.hom_ext
    · simp only [Category.assoc]
      rw [← hmm, hn'c, hl', reassoc_of% hys, ← C'.lv, hsm]
    · simp only [Category.assoc]
      rw [mm.cart.1.w, reassoc_of% (sec_hom _), sec_hom l']
      simp
  have I3 : ∀ y' : D.La, (W.o.eta ((algebraMap (𝓞 D.F) D.O) a • y')).left ≫ q3.φ =
      (y ≫ Lj.t) ≫ (S.Y.lv y').left := by
    intro y'
    obtain ⟨l', hl'⟩ := sec_lift Lj.ms.cart.1 (S.Y.lv y')
    have hTE := hTrEta p D G L E gb (h * u) _ _ N' N (T.M N').univ W.o W.ψ W.trans N t 1 hN't
      (_root_.mul_one _).symm _ _ (hx y')
    rw [one_smul] at hTE
    have hlv := Lj.lev y' l' hl'
    rw [Over.comp_left, Category.assoc] at hlv
    rw [← hTE, Over.comp_left, hq3]
    simp only [Category.assoc]
    rw [← reassoc_of% I2, reassoc_of% (I4 y' l' hl'), hlv]
  obtain ⟨l, hlev, hl⟩ := hQLev q _ _ _ _ _ _ _ _ a S.𝔞 hNpos hGen _ _ _ W.o o₂ n₂
  obtain ⟨f₀, -, huniq⟩ := S.Y.rep _ _ o₂ l hlev
  obtain ⟨q3c, hq3c⟩ := qcast (show y ≫ Lj.t = 𝟙 _ ≫ (y ≫ Lj.t) by simp) q3
  obtain ⟨μ2, hμ2⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ W.o o₂ S.Y.univ (𝟙 _) (y ≫ Lj.t)).2.2.1
    inferInstance n₂ q3c
  obtain ⟨qCc, hqCc⟩ := qcast (show W.π ≫ C.j = 𝟙 _ ≫ (W.π ≫ C.j) by simp) qC
  obtain ⟨μ1, hμ1⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ W.o o₂ S.Y.univ (𝟙 _) (W.π ≫ C.j)).2.2.1
    inferInstance n₂ qCc
  have base2 : (y ≫ Lj.t) ≫ S.Y.s = (C'.j ≫ S.π) ≫ S.M.s := by
    simp only [Category.assoc]
    rw [← S.ov, reassoc_of% Lj.tπ, ← Tj.st, reassoc_of% hyg, reassoc_of% hy₀]
  have base1 : (W.π ≫ C.j) ≫ S.Y.s = (C'.j ≫ S.π) ≫ S.M.s := by
    rw [e0, Category.assoc, C.ov, reassoc_of% W.ov]
  have eq2 := huniq _ ⟨base2, μ2, fun y' => by
    rw [← hl y', Category.assoc, ← hμ2, hq3c, I3 y']⟩
  have eq1 := huniq _ ⟨base1, μ1, fun y' => by
    rw [← hl y', Category.assoc, ← hμ1, hqCc, hqC, ← Category.assoc]
    erw [W.φ.eta]
    rw [Category.assoc, C.lv, Category.assoc]⟩
  have yt : y ≫ Lj.t = W.π ≫ C.j := eq2.trans eq1.symm
  obtain ⟨q3y, hq3y⟩ := qcast yt q3
  refine ⟨⟨y, hys, yt, mm, ?_, ?_⟩⟩
  · rw [← hmm, hn'c]
  · rw [reassoc_of% I2, ← hq3, ← hqC, ← hq3y, hQUniq q _ _ _ _ _ _ _ _ h3 hcq _ _ _ _ _ _ _ q3y qC]
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo

private theorem isIntAf_one' {p : ℕ} [Fact p.Prime] : IsIntAf (1 : AfP p) := fun v => by
  rw [map_one]; exact one_mem _

private theorem inAf_mem' {p : ℕ} [Fact p.Prime] {D : Datum p} (y : D.La) : inAf D y ∈ LaHat D :=
  AddSubgroup.subset_closure ⟨1, y, isIntAf_one', rfl⟩


theorem UpperTheory.quotient_invariant_of_trace_unit_crt :
    NumEx → QComp → QIso → ClsEx → TrEta → TrUnit → CongCRT → BaseInv := by
  intro hNumEx hQComp hQIso hClsEx hTrEta hTrUnit hCRT p _ D G L E _ _ gb w q _ r 𝔴 𝔫 S k T K₀ hLev N' N t c a hN't hNum C' C u hu W
  have hNpos : 0 < (N : ℕ) := by have := N.2.1; omega
  have hN'pos : 0 < (N' : ℕ) := by have := N'.2.1; omega
  have hNum' := (hNumEx p D E gb w q r 𝔴 𝔫 S (N : ℕ) hNpos).2 c a t hNum
  obtain ⟨hNc, hGen⟩ := hNum
  obtain ⟨-, hGen'⟩ := hNum'
  rw [← hN't] at hGen'
  have hN'c : (N' : ℕ) = S.N₀ * (c * t) := by rw [hN't, hNc, _root_.mul_assoc]
  have h3 : 3 ≤ S.N₀ := S.std.three
  have hcq : S.N₀.Coprime q := S.std.cop
  have hu1 := ((hLev u).mp hu).1
  have hIu : Integ L u := integ_of_mem hu1
  have hCRTu := hCRT p D G L q r S.N₀ S.𝔞 hcq S.upow u hIu
  have hC := hCRTu.1.mp (by have h1 := ((hLev u).mp hu).2; rwa [S.lev] at h1)
  have hEta : ∀ y : D.La, (T.M N').univ.eta ((c * t) • y) ≫ W.ψ = W.o.eta (c • y) := by
    intro y
    obtain ⟨v, hv, ev⟩ := hC.1 _ (inAf_mem' y)
    exact hTrEta p D G L E gb u _ _ N' N (T.M N').univ W.o W.ψ W.trans S.N₀ (c * t) c hN'c hNc y y ⟨v, hv, ev⟩
  obtain ⟨hIso, hLB⟩ := hTrUnit p D G L E gb u _ _ N' N (T.M N').univ W.o W.ψ W.trans hu1
  obtain ⟨qC, hqC⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ (T.M N).univ S.Y.univ S.Y.univ C.j (𝟙 _)).2.2.2
    _ _ W.o W.π W.φ C.m
  obtain ⟨n', hn'⟩ := hQIso q _ _ _ _ _ _ _ _ c (c * t) _ _ _ _ (T.M N').univ W.o S.Y.univ _ W.ψ hIso W.trans.1
    W.trans.2.1 hLB hEta qC
  have hov : (W.π ≫ C.j) ≫ S.Y.s = (T.M N').s ≫ spMap (algebraMap (Ow w) E) := by
    rw [Category.assoc, C.ov, reassoc_of% W.ov]
  have hlv : ∀ y : D.La, ((T.M N').univ.eta ((algebraMap (𝓞 D.F) D.O) (↑t * a) • y)).left ≫ n'.φ =
      (W.π ≫ C.j) ≫ (S.Y.lv y).left := by
    intro y
    have hsm : (algebraMap (𝓞 D.F) D.O (↑t * a)) • y = t • ((algebraMap (𝓞 D.F) D.O) a • y) := by
      rw [map_mul, map_natCast, mul_smul, Nat.cast_smul_eq_nsmul]
    obtain ⟨v₂, hv₂, e₂⟩ := (hCRTu.2 a N hNpos N.2.2 hGen).mp hC.2 y
    have hTE := hTrEta p D G L E gb u _ _ N' N (T.M N').univ W.o W.ψ W.trans N t 1 hN't
      (_root_.mul_one _).symm _ _ ⟨v₂, hv₂, e₂⟩
    rw [one_smul] at hTE
    rw [hsm, hn', hqC, ← Category.assoc, ← Over.comp_left, hTE, ← Category.assoc]
    erw [W.φ.eta]
    rw [Category.assoc, C.lv, Category.assoc]
  obtain ⟨-, huq⟩ := hClsEx q _ _ _ S.b gb _ S.mat _ _ _ _ _ hN'c hN'pos h3 hcq hGen' S.Y _ _ (T.M N').univ
  obtain ⟨hj, hm⟩ := huq ⟨W.π ≫ C.j, hov, n', hlv⟩ C'
  refine ⟨hj, ?_⟩
  calc Over.Hom.left W.ψ ≫ W.φ.φ ≫ C.m.φ = n'.φ := by rw [hn', hqC]
    _ = C'.m.φ := hm
end
