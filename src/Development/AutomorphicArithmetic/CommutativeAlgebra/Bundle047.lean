module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
import Mathlib.Algebra.AffineMonoid.Basic
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
import Mathlib.Tactic.Lemma
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

open UpperTheory.Gal.Int.Geo
open NumberField

private lemma natDvd_of_eq_mul {F : Type} [Field F] [NumberField F] {n m : ℕ} {x : 𝓞 F}
    (h : (n : 𝓞 F) * x = (m : 𝓞 F)) : n ∣ m := by
  have hd : Module.finrank ℤ (𝓞 F) ≠ 0 := Module.finrank_pos.ne'
  have hn := congrArg (Algebra.norm ℤ) h
  have e : ∀ k : ℕ, (k : 𝓞 F) = algebraMap ℤ (𝓞 F) (k : ℤ) := fun k => by simp
  rw [map_mul, e n, e m, Algebra.norm_algebraMap, Algebra.norm_algebraMap] at hn
  have hdvd : (n : ℤ) ^ Module.finrank ℤ (𝓞 F) ∣ (m : ℤ) ^ Module.finrank ℤ (𝓞 F) :=
    ⟨_, hn.symm⟩
  exact Int.natCast_dvd_natCast.1 ((Int.pow_dvd_pow_iff hd).1 hdvd)

theorem UpperTheory.exists_number_field_point_of_generic :
    GenEx → NumEx := by
  intro hG p _ D E _ _ gb w q _ r 𝔴 𝔫 S N hN
  refine ⟨fun hmem => ?_, fun c a t h => ?_⟩
  · rw [S.lev] at hmem
    obtain ⟨x, hx, hxe⟩ := Ideal.mem_span_singleton_mul.1 hmem
    have hNa : (N : 𝓞 D.F) ∈ S.𝔞 := hxe ▸ Ideal.mul_mem_left _ _ hx
    obtain ⟨a, ha⟩ := (hG (𝓞 D.F) S.𝔞 N hN).1 hNa
    obtain ⟨c, hc⟩ := natDvd_of_eq_mul hxe
    exact ⟨c, a, hc, ha⟩
  · exact ⟨by rw [h.1, mul_assoc], (hG (𝓞 D.F) S.𝔞 N hN).2 a t h.2⟩
end

section

set_option autoImplicit false

namespace UpperTheory

open UpperTheory.Gal.Int.Geo

theorem exists_generic_moduli_point : GenEx := by
  intro A _ _ _ 𝔞 N hN
  have hN0 : (N : A) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  refine ⟨fun hmem => ?_, fun a t h => ?_⟩
  · have hdvd : 𝔞 ∣ Ideal.span {(N : A)} :=
      Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hmem)
    obtain ⟨𝔟, h𝔟⟩ := hdvd
    have hle : Ideal.span {(N : A)} ≤ 𝔟 := by
      rw [h𝔟]; exact Ideal.mul_le_right
    have hne : Ideal.span {(N : A)} ≠ ⊥ := by
      simpa [Ideal.span_singleton_eq_bot] using hN0
    obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq hle hne
    refine ⟨a, ?_⟩
    unfold IsGen
    rw [sup_comm, ha, mul_comm, ← h𝔟]
  · unfold IsGen at h ⊢
    have hs : Ideal.span {(t : A) * a} ⊔ Ideal.span {((N * t : ℕ) : A)}
        = Ideal.span {(t : A)} * (Ideal.span {a} ⊔ Ideal.span {(N : A)}) := by
      rw [Ideal.mul_sup, Ideal.span_singleton_mul_span_singleton,
        Ideal.span_singleton_mul_span_singleton, Nat.cast_mul, mul_comm (N : A)]
    rw [hs, mul_assoc, h, Ideal.span_singleton_mul_span_singleton, Nat.cast_mul, mul_comm (N : A)]

end UpperTheory
end

section

open UpperTheory.Gal.Int.Geo

namespace UpperTheory.ActionSupremumCommute

variable {A O M : Type} [CommRing A] [Ring O] [Algebra A O] [AddCommGroup M] [Module O M]

private lemma nat_act (N : ℕ) (y : M) : algebraMap A O (N : A) • y = N • y := by
  rw [map_natCast, Nat.cast_smul_eq_nsmul]

private lemma act_comm (c d : A) (y : M) :
    algebraMap A O c • algebraMap A O d • y = algebraMap A O d • algebraMap A O c • y := by
  rw [smul_smul, smul_smul, ← map_mul, ← map_mul, mul_comm c d]

private lemma exists_sup {a b : A} {N : ℕ} (hb : b ∈ Ideal.span {a} ⊔ Ideal.span {(N : A)}) :
    ∃ r s : A, b = r * a + s * (N : A) := by
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hb
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hu
  obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.mp hv
  exact ⟨r, s, rfl⟩

private lemma act_sup {a b : A} {N : ℕ} (hb : b ∈ Ideal.span {a} ⊔ Ideal.span {(N : A)}) (w : M) :
    ∃ y z : M, algebraMap A O b • w = algebraMap A O a • y + N • z := by
  obtain ⟨r, s, rfl⟩ := exists_sup hb
  refine ⟨algebraMap A O r • w, algebraMap A O s • w, ?_⟩
  rw [map_add (f := _), add_smul, map_mul, map_mul, mul_smul, mul_smul, act_comm r a, act_comm s (N : A), nat_act]

private lemma act_sup_of {a b : A} {N : ℕ} (hb : b ∈ Ideal.span {a} ⊔ Ideal.span {(N : A)})
    {y z : M} (hy : algebraMap A O a • y = N • z) :
    ∃ z' : M, algebraMap A O b • y = N • z' := by
  obtain ⟨r, s, rfl⟩ := exists_sup hb
  refine ⟨algebraMap A O r • z + algebraMap A O s • y, ?_⟩
  rw [map_add (f := _), add_smul, map_mul, map_mul, mul_smul, mul_smul, hy, nat_act, smul_add,
    smul_comm N (algebraMap A O r) z, smul_comm N (algebraMap A O s) y]

private lemma fwd {a : A} {N : ℕ} {𝔞 : Ideal A}
    (h : (Ideal.span {a} ⊔ Ideal.span {(N : A)}) * 𝔞 = Ideal.span {(N : A)})
    (inj : ∀ u v : M, N • u = N • v → u = v) (W : Submodule O M)
    (hW : ∀ c ∈ 𝔞, ∀ z : M, algebraMap A O c • z ∈ W) {y z : M}
    (hy : algebraMap A O a • y = N • z) : y ∈ W := by
  have key : ∀ t ∈ (Ideal.span {a} ⊔ Ideal.span {(N : A)}) * 𝔞,
      ∃ u ∈ W, algebraMap A O t • y = N • u := by
    intro t ht
    refine Submodule.mul_induction_on ht ?_ ?_
    · intro b hb c hc
      obtain ⟨z', hz'⟩ := act_sup_of hb hy
      refine ⟨algebraMap A O c • z', hW c hc z', ?_⟩
      rw [mul_comm b c, map_mul, mul_smul, hz']
      exact smul_comm _ _ _
    · rintro t t' ⟨u, hu, hu'⟩ ⟨v, hv, hv'⟩
      exact ⟨u + v, W.add_mem hu hv, by rw [map_add (f := _), add_smul, hu', hv', smul_add]⟩
  obtain ⟨u, hu, hu'⟩ := key (N : A) (by rw [h]; exact Ideal.mem_span_singleton_self _)
  rw [nat_act] at hu'
  rwa [inj y u hu']

private lemma bwd {a : A} {N : ℕ} {𝔞 : Ideal A}
    (h : (Ideal.span {a} ⊔ Ideal.span {(N : A)}) * 𝔞 = Ideal.span {(N : A)}) {y : M}
    (hy : y ∈ Submodule.span O {z : M | ∃ c ∈ 𝔞 ^ 1, ∃ z' : M, z = algebraMap A O c • z'}) :
    ∃ z : M, algebraMap A O a • y = N • z := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, z', rfl⟩ := hx
    rw [pow_one] at hc
    have hac : a * c ∈ Ideal.span {(N : A)} :=
      h ▸ Ideal.mul_mem_mul (Ideal.mem_sup_left (Ideal.mem_span_singleton_self a)) hc
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hac
    refine ⟨algebraMap A O t • z', ?_⟩
    rw [← mul_smul, ← map_mul, ← ht, map_mul, mul_smul, act_comm t (N : A), nat_act]
  | zero => exact ⟨0, by simp⟩
  | add x x' _ _ hx hx' =>
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := hx'
    exact ⟨u + v, by rw [smul_add, hu, hv, smul_add]⟩
  | smul o x _ hx =>
    obtain ⟨u, hu⟩ := hx
    refine ⟨o • u, ?_⟩
    rw [← mul_smul, Algebra.commutes, mul_smul, hu]
    exact smul_comm _ _ _

private lemma part2 {a : A} {N : ℕ} {𝔞 : Ideal A}
    (h : (Ideal.span {a} ⊔ Ideal.span {(N : A)}) * 𝔞 = Ideal.span {(N : A)})
    (inj : ∀ u v : M, N • u = N • v → u = v) {x : M}
    (hx : ∀ c ∈ 𝔞, ∃ z : M, algebraMap A O c • x = N • z) :
    ∃ y z : M, x = algebraMap A O a • y + N • z := by
  have key : ∀ t ∈ (Ideal.span {a} ⊔ Ideal.span {(N : A)}) * 𝔞,
      ∃ y z : M, algebraMap A O t • x = N • (algebraMap A O a • y + N • z) := by
    intro t ht
    refine Submodule.mul_induction_on ht ?_ ?_
    · intro b hb c hc
      obtain ⟨z0, hz0⟩ := hx c hc
      obtain ⟨y, z, hyz⟩ := act_sup (O := O) hb z0
      refine ⟨y, z, ?_⟩
      rw [map_mul, mul_smul, hz0, ← hyz]
      exact smul_comm _ _ _
    · rintro t t' ⟨y, z, h1⟩ ⟨y', z', h2⟩
      refine ⟨y + y', z + z', ?_⟩
      rw [map_add (f := _), add_smul, h1, h2]
      simp only [smul_add]
      abel
  obtain ⟨y, z, hyz⟩ := key (N : A) (by rw [h]; exact Ideal.mem_span_singleton_self _)
  rw [nat_act] at hyz
  exact ⟨y, z, inj _ _ hyz⟩

end UpperTheory.ActionSupremumCommute

theorem UpperTheory.lattice_generation :
    LatGen := by
  intro q _ D a N 𝔞 hN hG
  haveI := D.freeLa
  have inj : ∀ u v : D.La, N • u = N • v → u = v := by
    intro u v huv
    have h0 : (N : ℤ) • (u - v) = 0 := by
      rw [smul_sub, natCast_zsmul, natCast_zsmul, huv, sub_self]
    rcases smul_eq_zero.mp h0 with h1 | h1
    · exact absurd (Int.natCast_eq_zero.mp h1) hN.ne'
    · exact sub_eq_zero.mp h1
  refine ⟨fun y => ⟨fun ⟨z, hz⟩ => UpperTheory.ActionSupremumCommute.fwd hG inj _ ?_ hz,
    fun hy => UpperTheory.ActionSupremumCommute.bwd hG hy⟩, fun x hx => UpperTheory.ActionSupremumCommute.part2 hG inj hx⟩
  intro c hc z
  exact Submodule.subset_span ⟨c, by rwa [pow_one], z, rfl⟩
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo

private lemma pullback_lift_clopen_immersion {W X Mη M P B B' Z : Scheme.{0}} (j : X ⟶ Mη) (f₁ : Mη ⟶ M) (f₂ : Mη ⟶ B') (s : M ⟶ B)
    (g : B' ⟶ B) (hp : IsPullback f₁ f₂ s g) (h : P ⟶ M) (w : W ⟶ X) (φ : W ⟶ P)
    (hc : IsPullback φ w h (j ≫ f₁)) (ε : Z ≅ W) (ρ : Z ⟶ P) (hρ : ρ = ε.hom ≫ φ) (t : Z ⟶ B')
    (ht : t = ε.hom ≫ w ≫ j ≫ f₂) (e : ρ ≫ h ≫ s = t ≫ g) [IsOpenImmersion j] [IsClosedImmersion j] :
    IsOpenImmersion (pullback.lift ρ t e) ∧ IsClosedImmersion (pullback.lift ρ t e) := by
  have hQ : IsPullback (pullback.fst (h ≫ s) g) (pullback.snd (h ≫ s) g) (h ≫ s) g :=
    IsPullback.of_hasPullback _ _
  have hu0 : (pullback.fst (h ≫ s) g ≫ h) ≫ s = pullback.snd (h ≫ s) g ≫ g := by
    rw [Category.assoc]; exact pullback.condition
  let u : pullback (h ≫ s) g ⟶ Mη := hp.lift (pullback.fst _ _ ≫ h) (pullback.snd _ _) hu0
  have hu1 : u ≫ f₁ = pullback.fst _ _ ≫ h := hp.lift_fst _ _ _
  have hu2 : u ≫ f₂ = pullback.snd _ _ := hp.lift_snd _ _ _
  have A : IsPullback u (pullback.fst (h ≫ s) g) f₁ h :=
    IsPullback.of_right (h₁₂ := f₂) (v₁₃ := g) (h₂₂ := s) (by rw [hu2]; exact hQ.flip) hu1 hp.flip
  have hφ : φ ≫ h ≫ s = (w ≫ j ≫ f₂) ≫ g := by
    rw [← Category.assoc, hc.w]
    simp only [Category.assoc, hp.w]
  let l : W ⟶ pullback (h ≫ s) g := pullback.lift φ (w ≫ j ≫ f₂) hφ
  have hl1 : l ≫ pullback.fst _ _ = φ := pullback.lift_fst _ _ _
  have hl2 : l ≫ pullback.snd _ _ = w ≫ j ≫ f₂ := pullback.lift_snd _ _ _
  have hlu : l ≫ u = w ≫ j := by
    apply hp.hom_ext
    · rw [Category.assoc, hu1, ← Category.assoc, hl1, hc.w, Category.assoc]
    · rw [Category.assoc, hu2, hl2, Category.assoc]
  have B1 : IsPullback l w u j :=
    IsPullback.of_right (h₁₂ := pullback.fst _ _) (v₁₃ := h) (h₂₂ := f₁) (by rw [hl1]; exact hc) hlu A.flip
  have o1 : IsOpenImmersion l := MorphismProperty.of_isPullback (P := @IsOpenImmersion) B1.flip inferInstance
  have o2 : IsClosedImmersion l := MorphismProperty.of_isPullback (P := @IsClosedImmersion) B1.flip inferInstance
  have hE : pullback.lift ρ t e = ε.hom ≫ l := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, hl1, hρ]
    · rw [pullback.lift_snd, Category.assoc, hl2, ht]
  rw [hE]
  exact ⟨inferInstance, inferInstance⟩

private lemma powMap_congr {S' S₁ : Scheme.{0}} {A' : Over S'} {A : Over S₁} {f f' : S' ⟶ S₁} {φ φ' : A'.left ⟶ A.left}
    (hf : f = f') (hφ : φ = φ') (h : φ ≫ A.hom = A'.hom ≫ f) (h' : φ' ≫ A.hom = A'.hom ≫ f') (m : ℕ) :
    GlobalTheory.KS.powMap f φ h m = GlobalTheory.KS.powMap f' φ' h' m := by
  subst hf; subst hφ; rfl

theorem UpperTheory.tower_trivial_of_quotient_trace_powerCartesian :
    MIn → QObj → QComp → QIso → QUniq → TrEta → TrUnit → PowCart → PiZero := by
  intro hM hQO hQC hQI hQU hTE hTU hPC p _ D G L E _ _ gb w q _ r 𝔴 𝔫 S k T N c a hNum C
  haveI : IsNoetherianRing (Ow w) := inferInstance
  let N₀' : Lv p := ⟨S.N₀, S.std.three, S.cop⟩
  let β : Ow w →+* E := algebraMap (Ow w) E
  obtain ⟨j₀, hop, hcl, hj, φA, φ₂, hcart, hsq, hact, ⟨hpol⟩, heta⟩ :=
    hM.cmp q (datAt S.atq S.sp) (Ow w) S.b E β gb S.mat.1 S.mat.2 S.N₀ S.std.three S.std.cop S.M (T.M N₀')
  let f₀ : (T.M N₀').X ⟶ S.M.X := j₀ ≫ pullback.fst _ _
  let n₀ : QMap (D := datAt S.atq S.sp) (gb := gb) (T.M N₀').univ S.M.univ f₀ 1 :=
    { φ := φA, φ₂ := φ₂, cart := hcart, sq := hsq, act := hact, pol := hpol,
      eta := fun y => by rw [one_smul]; exact heta y }
  let pw := GlobalTheory.KS.powMap f₀ n₀.φ n₀.cart.1.w k
  have pc := hPC _ _ _ (T.M N₀').univ.A S.M.univ.A S.M.univ.A f₀ (𝟙 _) n₀.φ (𝟙 _) n₀.cart.1.w (by simp) k
  have hs : f₀ ≫ S.M.s = (T.M N₀').s ≫ spMap β := by
    simp only [f₀, Category.assoc]
    rw [pullback.condition, ← Category.assoc, hj]
  have hq : T.X.q (T.lev N₀') = (T.e N₀').hom ≫ (GlobalTheory.KS.pow (T.M N₀').univ.A k).hom ≫ j₀ ≫ pullback.snd _ _ := by
    rw [hj, T.e_q]
  have e : ((T.e N₀').hom ≫ pw) ≫ (GlobalTheory.KS.pow S.M.univ.A k).hom ≫ S.M.s = T.X.q _ ≫ gen (Ow w) E := by
    rw [← T.e_q N₀']
    simp only [Category.assoc]
    rw [← Category.assoc pw, pc.2.1]
    simp only [Category.assoc]
    rw [hs]
  refine ⟨(T.e N₀').hom ≫ pw, e, ?_⟩
  haveI := hop
  haveI := hcl
  obtain ⟨h1, h2⟩ := pullback_lift_clopen_immersion j₀ (pullback.fst _ _) (pullback.snd _ _) S.M.s (spMap β)
    (IsPullback.of_hasPullback _ _) (GlobalTheory.KS.pow S.M.univ.A k).hom (GlobalTheory.KS.pow (T.M N₀').univ.A k).hom pw
    (pc.1 n₀.cart.1) (T.e N₀') _ rfl _ hq e
  refine ⟨h1, h2, fun x y => ?_⟩
  obtain ⟨π, o, ψ, φ, hw, hπs, htrans, htr⟩ := T.tr_eq N N₀' 1 x y
  obtain ⟨hiso, hlb⟩ := hTU p D G L E gb 1 _ _ N N₀' (T.M N).univ o ψ htrans (one_mem _)
  have heta' : ∀ y' : D.La, (T.M N).univ.eta (c • y') ≫ ψ = o.eta (1 • y') := fun y' =>
    hTE p D G L E gb 1 _ _ N N₀' (T.M N).univ o ψ htrans S.N₀ c 1 hNum.1 (_root_.mul_one _).symm y' y'
      ⟨0, zero_mem _, by simp⟩
  obtain ⟨n₁, hn₁⟩ := (hQC q (datAt S.atq S.sp) (Ow w) E S.b gb S.N₀ S.N₀ 1 _ _ _ (T.M N₀').s S.M.s S.M.s (T.M N₀').univ
    S.M.univ S.M.univ f₀ (𝟙 _)).2.2.2 _ (T.M N).s o π φ n₀
  obtain ⟨n₂, hn₂⟩ := hQI q (datAt S.atq S.sp) (Ow w) E S.b gb S.N₀ N.1 S.N₀ 1 c _ _ (T.M N).s S.M.s (T.M N).univ o
    S.M.univ (π ≫ f₀) ψ hiso htrans.1 htrans.2.1 hlb heta' n₁
  obtain ⟨n₃, hn₃⟩ := (hQC q (datAt S.atq S.sp) (Ow w) E S.b gb N.1 S.N₀ c _ _ _ (T.M N).s S.Y.s S.M.s (T.M N).univ
    S.Y.univ S.M.univ C.j S.π).1 C.m S.mπ
  obtain ⟨o₀, ⟨n₄⟩⟩ := hQO q (datAt S.atq S.sp) (Ow w) E S.b gb β S.mat N.1 S.N₀ c hNum.1 (by have := N.2.1; omega)
    S.std.cop _ (T.M N).s (T.M N).univ
  obtain ⟨f', -, huniq⟩ := S.M.rep _ ((T.M N).s ≫ spMap β) o₀
  have key : ∀ (g : (T.M N).X ⟶ S.M.X), QMap (D := datAt S.atq S.sp) (gb := gb) (T.M N).univ S.M.univ g c →
      g ≫ S.M.s = (T.M N).s ≫ spMap β → g = f' := by
    intro g n hg
    have n' : QMap (D := datAt S.atq S.sp) (gb := gb) (T.M N).univ S.M.univ (𝟙 _ ≫ g) c := by
      rw [Category.id_comp]; exact n
    obtain ⟨m, -⟩ := (hQC q (datAt S.atq S.sp) (Ow w) E S.b gb N.1 S.N₀ c _ _ _ (T.M N).s _ S.M.s (T.M N).univ
      o₀ S.M.univ (𝟙 _) g).2.2.1 inferInstance n₄ n'
    exact huniq g ⟨hg, ⟨m⟩⟩
  have hf : C.j ≫ S.π = π ≫ f₀ := by
    rw [key _ n₃ ?_, key _ n₂ ?_]
    · rw [Category.assoc, hs, ← Category.assoc, hπs]
    · rw [Category.assoc, S.ov, C.ov]
  have cast : ∀ {f f' : (T.M N).X ⟶ S.M.X} (_ : f = f')
      (n : QMap (D := datAt S.atq S.sp) (gb := gb) (T.M N).univ S.M.univ f c),
      ∃ n' : QMap (D := datAt S.atq S.sp) (gb := gb) (T.M N).univ S.M.univ f' c, n'.φ = n.φ := by
    intro f f' hff n
    subst hff
    exact ⟨n, rfl⟩
  obtain ⟨n₅, hn₅⟩ := cast hf n₃
  have hφ : C.m.φ ≫ S.mπ.φ = (ψ.left ≫ φ.φ) ≫ n₀.φ := by
    rw [← hn₃, ← hn₅, hQU q (datAt S.atq S.sp) (Ow w) E S.b gb N.1 S.N₀ c S.std.three S.std.cop _ _ (T.M N).s S.M.s
      (T.M N).univ S.M.univ (π ≫ f₀) n₅ n₂, hn₂, hn₁, Category.assoc]
  have hv1 : ((ψ.left ≫ φ.φ) ≫ n₀.φ) ≫ S.M.univ.A.hom = (T.M N).univ.A.hom ≫ π ≫ f₀ := by
    rw [Category.assoc, n₀.cart.1.w, ← Category.assoc, hw, Category.assoc]
  have hv2 : (C.m.φ ≫ S.mπ.φ) ≫ S.M.univ.A.hom = (T.M N).univ.A.hom ≫ C.j ≫ S.π := by
    rw [Category.assoc, S.mπ.cart.1.w, ← Category.assoc, C.m.cart.1.w, Category.assoc]
  have c1 := (hPC _ _ _ (T.M N).univ.A (T.M N₀').univ.A S.M.univ.A π f₀ (ψ.left ≫ φ.φ) n₀.φ hw n₀.cart.1.w k).2.2 hv1
  have c2 := (hPC _ _ _ (T.M N).univ.A S.Y.univ.A S.M.univ.A C.j S.π C.m.φ S.mπ.φ C.m.cart.1.w S.mπ.cart.1.w k).2.2 hv2
  change T.X.tr (T.lev N) (T.lev N₀') 1 x y ≫ (T.e N₀').hom ≫ pw =
    ((T.e N).hom ≫ GlobalTheory.KS.powMap C.j C.m.φ C.m.cart.1.w k) ≫ GlobalTheory.KS.powMap S.π S.mπ.φ S.mπ.cart.1.w k
  rw [← Category.assoc, htr, Category.assoc, Category.assoc, c1, c2]
  exact congrArg _ (powMap_congr hf.symm hφ.symm hv1 hv2 k)
end
end

section

open UpperTheory.Gal.Int.Geo

theorem UpperTheory.card_fiber_eq_relIndex_of_normal_quotient :
    ∀ (Γ : Type) [Group Γ] (K₀ H KN Km : Subgroup Γ), Count → Km ≤ KN → KN ≤ K₀ → Km ≤ H → H ≤ K₀ → (∀ k ∈ K₀, ∀ u ∈ Km, k * u * k⁻¹ ∈ Km) → Km.relIndex K₀ ≠ 0 → ∀ (V F : Type) (act : KN → V), Function.Surjective act → (∀ u u' : KN, act u = act u' ↔ (u : Γ)⁻¹ * u' ∈ Km) → ∀ (κ : (K₀ ⧸ KN.subgroupOf K₀) → V → F), Nat.card F = H.relIndex K₀ → (∀ (c₁ c₂ : K₀ ⧸ KN.subgroupOf K₀) (u₁ u₂ : KN), κ c₁ (act u₁) = κ c₂ (act u₂) → ((c₁.out : Γ) * u₁) * ((c₂.out : Γ) * u₂)⁻¹ ∈ H) → ∀ ζ : F, Nat.card {x : (K₀ ⧸ KN.subgroupOf K₀) × V // κ x.1 x.2 = ζ} = Km.relIndex H := by
  intro Γ _ K₀ H KN Km hC hmN hNK hmH hHK hn hidx V F act hs he κ hF sep ζ
  classical
  let cl : K₀ → (K₀ ⧸ KN.subgroupOf K₀) := fun x => ((x⁻¹ : K₀) : K₀ ⧸ KN.subgroupOf K₀)
  have hmem : ∀ x : K₀, ((cl x).out : Γ)⁻¹ * (x : Γ)⁻¹ ∈ KN := by
    intro x
    have h := QuotientGroup.eq.mp (QuotientGroup.out_eq' (cl x))
    simpa [Subgroup.mem_subgroupOf] using h
  let uu : K₀ → KN := fun x => ⟨((cl x).out : Γ)⁻¹ * (x : Γ)⁻¹, hmem x⟩
  have key : ∀ x : K₀, ((cl x).out : Γ) * (uu x : Γ) = (x : Γ)⁻¹ := by
    intro x
    show ((cl x).out : Γ) * (((cl x).out : Γ)⁻¹ * (x : Γ)⁻¹) = (x : Γ)⁻¹
    group
  have hcleq : ∀ x y : K₀, cl x = cl y → (uu x : Γ)⁻¹ * (uu y : Γ) = (x : Γ) * (y : Γ)⁻¹ := by
    intro x y h
    have hx := key x
    have hy := key y
    rw [h] at hx
    rw [eq_inv_mul_iff_mul_eq.mpr hx, eq_inv_mul_iff_mul_eq.mpr hy]
    group

  have hwd : ∀ x y : K₀, (x : Γ)⁻¹ * (y : Γ) ∈ Km → (cl x, act (uu x)) = (cl y, act (uu y)) := by
    intro x y h
    have h1 : (x : Γ) * (y : Γ)⁻¹ ∈ Km := by
      have := hn x x.2 _ (Km.inv_mem h)
      have e : (x : Γ) * ((x : Γ)⁻¹ * (y : Γ))⁻¹ * (x : Γ)⁻¹ = (x : Γ) * (y : Γ)⁻¹ := by group
      rwa [e] at this
    have hc : cl x = cl y := by
      refine QuotientGroup.eq.mpr ?_
      rw [Subgroup.mem_subgroupOf]
      simpa using hmN h1
    refine Prod.ext hc ?_
    show act (uu x) = act (uu y)
    rw [he, hcleq x y hc]
    exact h1
  let f : K₀ → (K₀ ⧸ KN.subgroupOf K₀) × V := fun x => (cl x, act (uu x))
  let Φ : (K₀ ⧸ Km.subgroupOf K₀) → (K₀ ⧸ KN.subgroupOf K₀) × V :=
    Quotient.lift f (fun a b hab => hwd a b (by
      have := QuotientGroup.leftRel_apply.mp hab
      simpa [Subgroup.mem_subgroupOf] using this))
  have hΦ : ∀ x : K₀, Φ (x : K₀ ⧸ Km.subgroupOf K₀) = (cl x, act (uu x)) := fun _ => rfl
  have hinj : Function.Injective Φ := by
    intro a b hab
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    rw [hΦ, hΦ] at hab
    have hc : cl x = cl y := congrArg Prod.fst hab
    have ha : act (uu x) = act (uu y) := congrArg Prod.snd hab
    rw [he, hcleq x y hc] at ha
    refine QuotientGroup.eq.mpr ?_
    rw [Subgroup.mem_subgroupOf]
    have := hn _ (K₀.inv_mem x.2) _ (Km.inv_mem ha)
    have e : (x : Γ)⁻¹ * ((x : Γ) * (y : Γ)⁻¹)⁻¹ * ((x : Γ)⁻¹)⁻¹ = (x : Γ)⁻¹ * (y : Γ) := by group
    rwa [e] at this
  have hsurj : Function.Surjective Φ := by
    rintro ⟨c, v⟩
    obtain ⟨u, rfl⟩ := hs v
    let x : K₀ := (c.out * (⟨u, hNK u.2⟩ : K₀))⁻¹
    refine ⟨(x : K₀ ⧸ Km.subgroupOf K₀), ?_⟩
    rw [hΦ]
    have hc : cl x = c := by
      have h1 : cl x = ((c.out * (⟨u, hNK u.2⟩ : K₀) : K₀) : K₀ ⧸ KN.subgroupOf K₀) := by
        show (((x⁻¹ : K₀)) : K₀ ⧸ KN.subgroupOf K₀) = _
        simp [x]
      rw [h1, ← QuotientGroup.out_eq' c]
      refine QuotientGroup.eq.mpr ?_
      rw [Subgroup.mem_subgroupOf]
      simp [Subgroup.mem_subgroupOf]
    refine Prod.ext hc ?_
    show act (uu x) = act u
    congr 1
    apply Subtype.ext
    have hx := key x
    rw [hc] at hx
    rw [eq_inv_mul_iff_mul_eq.mpr hx]
    simp [x]
  let E := Equiv.ofBijective Φ ⟨hinj, hsurj⟩
  have hcount := hC Γ K₀ H Km hmH hHK hidx F (fun a => κ (Φ a).1 (Φ a).2) hF (by
    intro x y h
    rw [hΦ, hΦ] at h
    have := sep _ _ _ _ h
    rw [key x, key y] at this
    simpa using this) ζ
  rw [← hcount]
  exact Nat.card_congr (Equiv.subtypeEquiv E (fun a => Iff.rfl)).symm
end

section

open UpperTheory.Gal.Int.Geo
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo

theorem UpperTheory.isogeny_class_exists_of_quotient :
    QObj → QComp → QUniq → QLev → ClsEx := by
  intro hObj hComp hUniq hLev q _ D R R' _ _ _ b gb β hM N N₀ c a 𝔞 hN hpos h3 hcop hgen Y X s o
  obtain ⟨o₀, ⟨n⟩⟩ := hObj q D R R' b gb β hM N N₀ c hN hpos hcop X s o
  obtain ⟨l, hl, hln⟩ := hLev q D R R' b gb N N₀ c a 𝔞 hpos hgen X s _ o o₀ n
  obtain ⟨f, ⟨hfs, m, hm⟩, hfu⟩ := Y.rep X _ o₀ l hl
  have key : ∀ (j : X ⟶ Y.X), j ≫ Y.s = s ≫ spMap β → ∀ (k : QMap o Y.univ j c),
      (∀ y : D.La, Over.Hom.left (o.eta ((algebraMap (NumberField.RingOfIntegers D.F) D.O) a • y)) ≫ k.φ =
        j ≫ Over.Hom.left (Y.lv y)) → j = f := by
    intro j hj k hk
    obtain ⟨k', hk'⟩ : ∃ k' : QMap o Y.univ (𝟙 X ≫ j) c, k'.φ = k.φ := by
      rw [Category.id_comp]
      exact ⟨k, rfl⟩
    obtain ⟨m', hm'⟩ :=
      (hComp q D R R' b gb N N₀ c X X Y.X s _ _ o o₀ Y.univ (𝟙 X) j).2.2.1 inferInstance n k'
    apply hfu
    refine ⟨hj, m', fun y => ?_⟩
    rw [← hln y, Category.assoc, ← hm', hk']
    exact hk y
  obtain ⟨n', hn'⟩ := (hComp q D R R' b gb N N₀ c X X Y.X s _ _ o o₀ Y.univ (𝟙 X) f).1 n m
  refine ⟨⟨⟨𝟙 X ≫ f, by rw [Category.id_comp, hfs], n', fun y => ?_⟩⟩, ?_⟩
  · rw [hn', ← Category.assoc, hln y, hm y, Category.id_comp]
  · intro C C'
    obtain ⟨j, ov, k, hk⟩ := C
    obtain ⟨j', ov', k', hk'⟩ := C'
    have e1 := key j ov k hk
    have e2 := key j' ov' k' hk'
    subst e1
    subst e2
    exact ⟨rfl, hUniq q D R R' b gb N N₀ c h3 hcop X Y.X s Y.s o Y.univ _ k k'⟩
end
