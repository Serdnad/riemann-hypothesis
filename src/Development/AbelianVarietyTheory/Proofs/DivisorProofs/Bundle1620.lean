module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle043
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle023
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle082
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1580
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1572
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeFactorFormGroupBoundedOfTestSupport
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

namespace GlobalTheory.AdMark

open scoped Matrix

theorem exists_lift {R S La U A : Type} [CommRing R] [CommRing S] [AddCommGroup La] [Module R La] [Module.Projective R La]
    [AddCommGroup U] [Module R U] [AddCommGroup A] [Module S A] (φ : R → S) (fv : U →+ A)
    (hfv : ∀ c x, fv (c • x) = φ c • fv x) (K : A →ₗ[S] A) (hKi : Function.Injective K) (H₁ Hk : AddSubgroup A)
    (hsm : ∀ c, ∀ z ∈ Hk, φ c • z ∈ Hk) (L : Submodule R U) (ι : La →ₗ[R] U) (hι : Function.Injective ι) (N : ℕ)
    (hL : ∀ v, v ∈ L ↔ fv v ∈ Hk) (hK : ∀ z, z ∈ Hk ↔ ∃ y ∈ H₁, K y = z)
    (h1 : ∀ v, fv v ∈ H₁ ↔ ∃ a, ι a = v)
    (ap1 : ∀ y ∈ H₁, ∃ a, ∃ w ∈ H₁, y = fv (ι a) + N • w)
    (apk : ∀ z ∈ Hk, ∃ x ∈ L, ∃ w ∈ Hk, z = fv x + N • w)
    (hdiv : ∀ x z, fv x = N • z → ∃ w, fv w = z ∧ x = N • w) :
    ∃ mk : La →ₗ[R] U, (∀ a, mk a ∈ L) ∧ (∀ a, ∃ w ∈ Hk, fv (mk a) - K (fv (ι a)) = N • w) ∧
      (∀ a, (∃ u ∈ L, mk a = N • u) → ∃ b, a = N • b) ∧ ∀ v ∈ L, ∃ a, ∃ u ∈ L, v = mk a + N • u := by
  let P : Submodule R (U × La) :=
    { carrier := {p | p.1 ∈ L ∧ ∃ w ∈ Hk, fv p.1 - K (fv (ι p.2)) = N • w}
      zero_mem' := ⟨L.zero_mem, 0, zero_mem _, by simp⟩
      add_mem' := by
        rintro p q ⟨hp, w, hw, e⟩ ⟨hq, w', hw', e'⟩
        refine ⟨L.add_mem hp hq, w + w', add_mem hw hw', ?_⟩
        rw [smul_add, ← e, ← e']
        simp only [Prod.fst_add, Prod.snd_add, map_add (f := _)]
        abel
      smul_mem' := by
        rintro c p ⟨hp, w, hw, e⟩
        refine ⟨L.smul_mem c hp, φ c • w, hsm c w hw, ?_⟩
        rw [smul_comm N, ← e]
        simp only [Prod.smul_fst, Prod.smul_snd, map_smul, hfv, smul_sub] }
  have hs : Function.Surjective ((LinearMap.snd R U La) ∘ₗ P.subtype) := by
    intro a
    obtain ⟨x, hx, w, hw, e⟩ := apk _ ((hK _).2 ⟨_, (h1 _).2 ⟨a, rfl⟩, rfl⟩)
    exact ⟨⟨(x, a), hx, -w, neg_mem hw, by rw [e]; simp⟩, rfl⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property _ LinearMap.id hs
  have hs2 : ∀ a, (s a).1.2 = a := fun a => LinearMap.congr_fun hs a
  let mk : La →ₗ[R] U := (LinearMap.fst R U La) ∘ₗ P.subtype ∘ₗ s
  have m1 : ∀ a, mk a ∈ L := fun a => (s a).2.1
  have m2 : ∀ a, ∃ w ∈ Hk, fv (mk a) - K (fv (ι a)) = N • w := fun a => by
    obtain ⟨w, hw, e⟩ := (s a).2.2
    rw [hs2] at e
    exact ⟨w, hw, e⟩
  refine ⟨mk, m1, m2, ?_, ?_⟩
  · rintro a ⟨u, hu, e⟩
    obtain ⟨w, hw, e'⟩ := m2 a
    obtain ⟨y, hy, ey⟩ := (hK _).1 (sub_mem ((hL u).1 hu) hw)
    have : fv (ι a) = N • y := by
      apply hKi
      rw [map_nsmul, ey, smul_sub, ← e', e, map_nsmul]
      abel
    obtain ⟨x, rfl, ex⟩ := hdiv _ _ this
    obtain ⟨b, rfl⟩ := (h1 _).1 hy
    exact ⟨b, hι (by rw [ex, map_nsmul])⟩
  · intro v hv
    obtain ⟨y, hy, ey⟩ := (hK _).1 ((hL v).1 hv)
    obtain ⟨a, w, hw, rfl⟩ := ap1 y hy
    obtain ⟨w', hw', e'⟩ := m2 a
    obtain ⟨u, hu, eu⟩ := hdiv (v - mk a) (K w - w') (by
      rw [map_sub, ← ey, smul_sub, ← e', map_add (f := _), map_nsmul]
      abel)
    refine ⟨a, u, (hL u).2 (hu ▸ sub_mem ((hK _).2 ⟨w, hw, rfl⟩) hw'), ?_⟩
    rw [← eu]
    abel

theorem sub_congr {A : Type} [AddCommGroup A] {x y z w w' : A} {M N c : ℕ} (hc : N = M * c) (e : y - z = M • w)
    (e' : x - z = N • w') : x - y = M • (c • w' - w) := by
  rw [smul_sub, ← mul_smul, ← hc, ← e, ← e']
  abel

end GlobalTheory.AdMark

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdMark

theorem latR_rfl {E : Type} [Field E] [NumberField E] {m : ℕ} (L : Submodule (𝓞 E) (Fin m → E)) :
    latR rfl L = L := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact hw
  · intro hv
    exact ⟨v, hv, rfl⟩

theorem smul_mem_latGHat {D : D7} (W : HSp D) (k : GA D W) (c : 𝓞 D.host.E) :
    ∀ z ∈ latGHat W k, ((1 : Af D.host.F) ⊗ₜ[D.host.F] (c : D.host.E)) • z ∈ latGHat W k := by
  intro z hz
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, z, hz, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨c • a, (D.host.AA : Submodule (𝓞 D.host.E) D.host.E).smul_mem c ha, z, hz, ?_⟩
    funext i
    rw [Pi.smul_apply, smul_eq_mul, ← _root_.mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one]
    rfl
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem exists_marking : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (l l₂ : Geo.Tor.Level H) (W : HSp D) (r : ℕ) (hr : W.rank = r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)), LatEmb W ι → l.M ∣ l₂.M → l₂.Mb ≤ l.Mb → ∀ k : GA D W, ∃ mk₂ : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E), IsMark l₂ (latR hr (latG W k)) mk₂ ∧ MarkAd l₂ W hr ι k mk₂ ∧ ∀ mk, (∀ a, mk a ∈ latR hr (latG W k)) → MarkAd l W hr ι k mk → MarkOver l l₂ (latR hr (latG W k)) mk mk₂ := by
  intro D H Dw l l₂ W r hr ι hι hM hMb k
  subst hr
  rw [latR_rfl]
  haveI := Dw.proj
  have hM0 : l.M ≠ 0 := by have := l.three_le; omega
  have hM2 : l₂.M ≠ 0 := by have := l₂.three_le; omega
  let fv : (Fin W.rank → D.host.E) →+ (Fin W.rank → Af D.host.F ⊗[D.host.F] D.host.E) :=
    AddMonoidHom.mk' (finVec W) (GlobalTheory.AdLat.cap_fv_add D.host.F)
  have ap : ∀ g : GA D W, ∀ z ∈ latGHat W g, ∃ x ∈ latG W g, ∃ w ∈ latGHat W g, z = fv x + l₂.M • w := by
    intro g
    obtain ⟨a1, a2, -, -, a5, -⟩ := GlobalTheory.Member.latG_lattice_and_completion D W g
    rw [a5]
    exact (GlobalTheory.AdLat.hat_rational_points_and_approx _ _ _ _ a1 a2).2.1 l₂.M (Nat.pos_of_ne_zero hM2)
  obtain ⟨mk₂, m1, m2, m3, m4⟩ := exists_lift (fun c : 𝓞 D.host.E => (1 : Af D.host.F) ⊗ₜ[D.host.F] (c : D.host.E)) fv
    (fun c x => by
      funext i
      change (1 : Af D.host.F) ⊗ₜ[D.host.F] ((c : D.host.E) * x i) = _ * ((1 : Af D.host.F) ⊗ₜ[D.host.F] x i)
      rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one])
    (finHom W k).1.mulVecLin
    (fun x y h => by
      have := congrArg (fun v => ((finHom W k)⁻¹).1 *ᵥ v) h
      simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] using this)
    (latGHat W 1) (latGHat W k) (smul_mem_latGHat W k) (latG W k) ι hι.1 l₂.M
    (GlobalTheory.MarkCoset.latG_spec D W k).1 (GlobalTheory.MarkCoset.latG_spec D W k).2
    (fun v => ((GlobalTheory.MarkCoset.latG_spec D W 1).1 v).symm.trans (by rw [← hι.2]; rfl))
    (fun y hy => by
      obtain ⟨x, hx, h⟩ := ap 1 y hy
      rw [← hι.2] at hx
      obtain ⟨a, rfl⟩ := hx
      exact ⟨a, h⟩)
    (ap k) (GlobalTheory.MarkCoset.finVec_div W l₂.M hM2)
  refine ⟨mk₂, ⟨m1, fun a _ => m3 a, fun v hv => ?_⟩, fun a _ => m2 a, fun mk _ hmk a ha => ?_⟩
  · refine Submodule.smul_induction_on hv (fun m hm v hv => ?_) (fun x y hx hy => ?_)
    · obtain ⟨a, u, hu, rfl⟩ := m4 v hv
      refine ⟨m • a, Submodule.smul_mem_smul hm trivial, m • u, Submodule.smul_mem _ m hu, ?_⟩
      rw [smul_add, map_smul, smul_comm m]
    · obtain ⟨a, ha, u, hu, rfl⟩ := hx
      obtain ⟨a', ha', u', hu', rfl⟩ := hy
      exact ⟨a + a', add_mem ha ha', u + u', add_mem hu hu', by rw [map_add (f := _), smul_add]; abel⟩
  · obtain ⟨c, hc⟩ := hM
    obtain ⟨w, hw, e⟩ := hmk a (Submodule.smul_mono_left (Ideal.map_mono hMb) ha)
    obtain ⟨w', hw', e'⟩ := m2 a
    replace e : fv (mk a) - (finHom W k).1.mulVecLin (fv (ι a)) = l.M • w := e
    obtain ⟨u, hu, eu⟩ := GlobalTheory.MarkCoset.finVec_div W l.M hM0 (mk₂ a - mk a) (c • w' - w) (by
      exact (fv.map_sub _ _).trans (sub_congr hc e e'))
    refine ⟨u, ((GlobalTheory.MarkCoset.latG_spec D W k).1 u).2 (hu ▸ sub_mem (nsmul_mem hw' c) hw), ?_⟩
    rw [← eu]
    abel

end GlobalTheory.AdMark
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKCx

theorem fixL_pos_unique_of_sep : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F), sigPosH (G.gram_herm v) = 1 →
    ∀ (β : G.Cˣ), sh G β = β → (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → ∀ y₀ : grp G β,
    (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n →
    (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable →
    ∀ z z' : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re → 0 < (star z' ⬝ᵥ (herm G v β *ᵥ z')).re →
    FixL G v β y₀ z → FixL G v β y₀ z' → ∃ c : ℂ, z' = c • z := by
  intro p _ G v hsig β hsh hR y₀ hdeg hsep z z' hz hz' hf hf'
  obtain ⟨_, _, Z, hZ⟩ := GlobalTheory.LKCx.herm_laws p G v β hsh hR
  set g0 : Matrix (Fin G.n) (Fin G.n) ℂ := (toV G v β y₀ : Matrix (Fin G.n) (Fin G.n) ℂ) with hg0
  set Zm : Matrix (Fin G.n) (Fin G.n) ℂ := (Z : Matrix (Fin G.n) (Fin G.n) ℂ) with hZm
  set Zi : Matrix (Fin G.n) (Fin G.n) ℂ := ((Z⁻¹ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) with hZi
  have hZiZ : Zi * Zm = 1 := by rw [hZi, hZm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hZZi : Zm * Zi = 1 := by rw [hZi, hZm, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  set s : ℝ := ((((y₀ : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) with hs
  have hspos : 0 < s := by rw [hs]; exact_mod_cast y₀.2.2
  have hsim0 := GlobalTheory.LKCx.grp_similitude_herm p G v β y₀
  set g : Matrix (Fin G.n) (Fin G.n) ℂ := Zm * g0 * Zi with hg
  have hsim : gᴴ * G.gram v * g = (s : ℂ) • G.gram v := by
    have e1 : gᴴ * G.gram v * g = Ziᴴ * (g0ᴴ * (Zmᴴ * G.gram v * Zm) * g0) * Zi := by
      rw [hg, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    rw [e1, ← hZ, hsim0]
    have e2 : Ziᴴ * ((((((y₀ : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℂ)) • herm G v β) * Zi =
        (s : ℂ) • ((Zm * Zi)ᴴ * G.gram v * (Zm * Zi)) := by
      rw [hZ, Matrix.mul_smul, Matrix.smul_mul, Matrix.conjTranspose_mul]
      congr 1
      simp only [Matrix.mul_assoc]
    rw [e2, hZZi, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hcp : g.charpoly.Separable := by
    have e : g = (Z : Matrix (Fin G.n) (Fin G.n) ℂ) * g0 * ((Z⁻¹ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) := rfl
    rw [e, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
    exact GlobalTheory.LKMid.charpoly_psi_separable p G v _ hdeg hsep
  have hpos : ∀ w : Fin G.n → ℂ, star (Zm *ᵥ w) ⬝ᵥ G.gram v *ᵥ (Zm *ᵥ w) = star w ⬝ᵥ (herm G v β *ᵥ w) := by
    intro w; rw [hZ, GlobalTheory.form_conjTranspose_mul_mul]
  have heig : ∀ w : Fin G.n → ℂ, FixL G v β y₀ w → ∃ μ : ℂ, g *ᵥ (Zm *ᵥ w) = μ • (Zm *ᵥ w) := by
    rintro w ⟨μ, hμ⟩
    refine ⟨μ, ?_⟩
    rw [hg, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hZiZ, Matrix.mul_one,
      ← Matrix.mulVec_mulVec, hμ, Matrix.mulVec_smul]
  obtain ⟨c, hc⟩ := GlobalTheory.eigvec_pos_unique_of_similitude (G.gram v) (G.gram_herm v) (G.gram_det v) hsig g s hspos
    hsim hcp (Zm *ᵥ z) (Zm *ᵥ z') (by rw [hpos]; exact hz) (by rw [hpos]; exact hz') (heig z hf) (heig z' hf')
  refine ⟨c, ?_⟩
  have := congrArg (Zi *ᵥ ·) hc
  simp only [Matrix.mulVec_mulVec, hZiZ, Matrix.one_mulVec, Matrix.mulVec_smul] at this
  exact this

end GlobalTheory.LKCx
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.similitudeFactor_formGroup_bounded_of_test_support : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), ∃ S : ℝ, ∀ (y : grp G β) (h₁ : G.GAf) (h₂ : Gr G 1), f (h₁⁻¹ * toAfF G β x t hx y * h₁) ≠ 0 → f' (h₂⁻¹ * toP1 G β y * h₂) ≠ 0 → (((y : G.Cˣ × ℚˣ).2 : ℚ) : ℝ) ≤ S := by
  first | (exact @GlobalTheory.SimBound.main) | (exact GlobalTheory.SimBound.main) | (intros; apply GlobalTheory.SimBound.main  <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

namespace GlobalTheory.HSCore.SplitField

theorem exists_algHom_factor (E A : Type) [Field E] [CommRing A] [Algebra E A] [Module.Finite E A] :
    ∃ p : Polynomial E, ∀ (Ω : Type) [Field Ω] [Algebra E Ω] [Algebra p.SplittingField Ω]
      [IsScalarTower E p.SplittingField Ω] (φ : A →ₐ[E] Ω),
      ∃ φ₀ : A →ₐ[E] p.SplittingField, ∀ a, φ a = algebraMap p.SplittingField Ω (φ₀ a) := by
  classical
  obtain ⟨t, ht⟩ := Module.Finite.fg_top (R := E) (M := A)
  obtain ⟨p, hp⟩ : ∃ p : Polynomial E, p = ∏ a ∈ t, minpoly E a := ⟨_, rfl⟩
  refine ⟨p, fun Ω _ _ _ _ φ => ?_⟩
  have hp0 : p ≠ 0 := hp ▸ Finset.prod_ne_zero_iff.2 fun a _ => minpoly.ne_zero (Algebra.IsIntegral.isIntegral a)
  let j : p.SplittingField →ₐ[E] Ω := IsScalarTower.toAlgHom E p.SplittingField Ω
  have hj : Function.Injective j := j.toRingHom.injective
  have hgen : ∀ a ∈ t, φ a ∈ j.range := fun a ha => by
    have h0 : Polynomial.aeval (φ a) p = 0 := by
      rw [Polynomial.aeval_algHom_apply, hp, map_prod, Finset.prod_eq_zero ha (minpoly.aeval E a), map_zero]
    have hs := Polynomial.SplittingField.splits p
    have hr : φ a ∈ ((p.map (algebraMap E p.SplittingField)).map (algebraMap p.SplittingField Ω)).roots := by
      rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq, Polynomial.mem_roots (Polynomial.map_ne_zero hp0),
        Polynomial.IsRoot.def, Polynomial.eval_map_algebraMap]
      exact h0
    rw [hs.roots_map] at hr
    obtain ⟨b, -, hb⟩ := Multiset.mem_map.1 hr
    exact ⟨b, hb⟩
  have hall : ∀ a, φ a ∈ j.range := fun a => by
    have ha : a ∈ Submodule.span E (t : Set A) := ht ▸ trivial
    induction ha using Submodule.span_induction with
    | mem x hx => exact hgen x hx
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact Subalgebra.smul_mem _ hx c
  refine ⟨(AlgEquiv.ofInjective j hj).symm.toAlgHom.comp (φ.codRestrict j.range hall), fun a => ?_⟩
  exact (congrArg Subtype.val ((AlgEquiv.ofInjective j hj).apply_symm_apply ⟨φ a, hall a⟩)).symm

theorem exists_point_factor (E : Type) [Field E] {Z : Scheme.{0}} (f : Z ⟶ Sp E) [IsFinite f] :
    ∃ p : Polynomial E, ∀ (Ω : Type) [Field Ω] [Algebra E Ω] [Algebra p.SplittingField Ω]
      [IsScalarTower E p.SplittingField Ω] (z : Sp Ω ⟶ Z), z ≫ f = spMap (algebraMap E Ω) →
      ∃ z₀ : Sp p.SplittingField ⟶ Z, z₀ ≫ f = spMap (algebraMap E p.SplittingField) ∧
        z = spMap (algebraMap p.SplittingField Ω) ≫ z₀ := by
  have : IsAffine Z := isAffine_of_isAffineHom f
  obtain ⟨g, hg⟩ := Spec.map_surjective (R := CommRingCat.of E) (Z.isoSpec.inv ≫ f)
  have hfin : g.hom.Finite := (IsFinite.SpecMap_iff g).1 (hg ▸ inferInstance)
  let : Algebra E Γ(Z, ⊤) := g.hom.toAlgebra
  have : Module.Finite E Γ(Z, ⊤) := hfin
  obtain ⟨p, hp⟩ := exists_algHom_factor E Γ(Z, ⊤)
  refine ⟨p, fun Ω _ _ _ _ z hz => ?_⟩
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (S := CommRingCat.of Ω) (z ≫ Z.isoSpec.hom)
  have hc : g ≫ ψ = CommRingCat.ofHom (algebraMap E Ω) := Spec.map_injective (by
    rw [Spec.map_comp, hg, hψ, Category.assoc, Iso.hom_inv_id_assoc, hz])
  obtain ⟨φ₀, h₀⟩ := hp Ω { ψ.hom with commutes' := fun a => congrArg (fun q => q.hom a) hc }
  refine ⟨Spec.map (CommRingCat.ofHom φ₀.toRingHom) ≫ Z.isoSpec.inv, ?_, ?_⟩
  · rw [Category.assoc, ← hg, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun a => φ₀.commutes a))
  · rw [← Category.assoc, Iso.eq_comp_inv, ← hψ, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun a => h₀ a))

theorem mem_subPts_iff_of_toBase_eq {F : Type} [Field F] (S : LinSys F) (E E' : Type) [Field E] [Field E'] [Algebra F E]
    [Algebra F E'] [Algebra E E'] {ι : Type} (s : ι → Fin S.N → E)
    {Ω : Type} [Field Ω] [Algebra E Ω] [Algebra E' Ω] [Algebra F Ω] [IsScalarTower F E Ω] [IsScalarTower F E' Ω]
    [IsScalarTower E E' Ω] (x : (S.baseChange E).Pt Ω) (x' : (S.baseChange E').Pt Ω)
    (h : LinSys.toBase x = LinSys.toBase x') :
    x ∈ (S.baseChange E).subPts ((S.baseChange E).cut s) Ω ↔
      x' ∈ (S.baseChange E').subPts ((S.baseChange E').cut fun i k => algebraMap E E' (s i k)) Ω := by
  refine (S.mem_subPts_cut_baseChange_iff E s x).trans
    (Iff.trans ?_ (S.mem_subPts_cut_baseChange_iff E' (fun i k => algebraMap E E' (s i k)) x').symm)
  rw [h]
  simp only [← IsScalarTower.algebraMap_apply]

end GlobalTheory.HSCore.SplitField

namespace GlobalTheory.HSCore


open SplitField in
theorem exists_split : ∀ (F : Type) [Field F] [NumberField F] (T : Tuple F) (E : Type) [Field E] [NumberField E] [Algebra F E] (s : Fin T.D → Fin T.N → E), T.IsGoodSection E s → ∃ (E' : Type) (_ : Field E') (_ : NumberField E') (_ : Algebra F E') (_ : Algebra E E') (_ : IsScalarTower F E E'), Split T E' fun i k => algebraMap E E' (s i k) := by
  intro F _ _ T E _ _ _ s hs
  have hfin : IsFinite ((T.linSection E s).subschemeι ≫ (T.toLinSys.baseChange E).str) := hs.finiteEtale.finite
  obtain ⟨p, hp⟩ := exists_point_factor E ((T.linSection E s).subschemeι ≫ (T.toLinSys.baseChange E).str)
  refine ⟨p.SplittingField, inferInstance, NumberField.of_module_finite E _, inferInstance, inferInstance,
    inferInstance, fun x hx => ?_⟩
  let x' : (T.toLinSys.baseChange p.SplittingField).Pt (AlgebraicClosure p.SplittingField) :=
    ⟨x ≫ Scheme.IdealSheafData.subschemeι _, (Category.assoc _ _ _).trans hx⟩
  obtain ⟨y, hy⟩ := (T.toLinSys.toBase_bijective E (AlgebraicClosure p.SplittingField)).2 (LinSys.toBase x')
  obtain ⟨z, hz⟩ := (mem_subPts_iff_of_toBase_eq T.toLinSys E p.SplittingField s y x' hy).2 ⟨x, rfl⟩
  obtain ⟨z₀, h₀, h₁⟩ := hp (AlgebraicClosure p.SplittingField) z (by
    rw [← Category.assoc]; exact (congrArg (· ≫ _) hz).trans y.2)
  let y₀ : (T.toLinSys.baseChange E).Pt p.SplittingField :=
    ⟨z₀ ≫ Scheme.IdealSheafData.subschemeι _, (Category.assoc _ _ _).trans h₀⟩
  obtain ⟨x₁, hx₁⟩ := (T.toLinSys.toBase_bijective p.SplittingField p.SplittingField).2 (LinSys.toBase y₀)
  obtain ⟨x₀, hx₀⟩ := (mem_subPts_iff_of_toBase_eq T.toLinSys E p.SplittingField s y₀ x₁ hx₁.symm).1 ⟨z₀, rfl⟩
  refine ⟨x₀, ?_⟩
  refine (cancel_mono (Scheme.IdealSheafData.subschemeι _)).1 ?_
  refine Eq.trans ?_ ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hx₀)).symm
  refine (T.toLinSys.isPullback_baseChange p.SplittingField).hom_ext ?_ ?_
  · have e₁ : x₁.1 ≫ T.toLinSys.bcFst _ = y₀.1 ≫ T.toLinSys.bcFst _ := congrArg Subtype.val hx₁
    have e₂ : y.1 ≫ T.toLinSys.bcFst _ = x'.1 ≫ T.toLinSys.bcFst _ := congrArg Subtype.val hy
    refine e₂.symm.trans ?_
    rw [Category.assoc, e₁, ← hz, h₁, Category.assoc, Category.assoc]
    rfl
  · refine x'.2.trans ?_
    rw [Category.assoc, x₁.2, ← Spec.map_comp]
    rfl

end GlobalTheory.HSCore
end
end

section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSCore

theorem spaceP_le_filTop {K : Type} [Field K] [NumberField K] (X : Data K) (s : Fin X.D → Fin X.N → K) :
    spaceP X s ≤ filTop X.str (X.adj X.T) X.U (X.ideal s) (X.T - X.D) := by
  unfold spaceP
  refine iSup_le fun α => ?_
  rintro _ ⟨m, -, rfl⟩
  exact vanishesTo_mulMono _ _ _ α _ m

theorem fil_spaceV_eq_spaceP (hF : FilMono) (K : Type) [Field K] [NumberField K] (X : Data K)
    (s : Fin X.D → Fin X.N → K) (hs : X.IsGood s) (hn : IsNef K X.LA) (hb : IsBig K X.LA) :
    Fil (X.ideal s) (X.T - X.D) (spaceV X s) = spaceP X s := by
  apply le_antisymm
  · rintro f ⟨hfV, hfv⟩
    obtain ⟨g, hg, p, hp, rfl⟩ := Submodule.mem_sup.1 hfV
    have hpv : VanishesTo (X.ideal s) (X.T - X.D) p := spaceP_le_filTop X s hp
    have hgv : VanishesTo (X.ideal s) (X.T - X.D) g := by
      have : g = (g + p) - p := by abel
      rw [this]
      exact (filTop X.str (X.adj X.T) X.U (X.ideal s) (X.T - X.D)).sub_mem hfv hpv
    obtain ⟨m, hm, hgm⟩ := hF K X.toGeo hn hb s hs (X.T - X.D) X.D X.T (add_sub_D X) (Nat.le_refl _) g ⟨hg, hgv⟩
    refine (spaceP X s).add_mem ?_ hp
    rw [hgm]
    refine Submodule.sum_mem _ fun α _ => ?_
    unfold spaceP
    exact Submodule.mem_iSup_of_mem α ⟨m α, X.global_le X.D (by have := X.le_T; omega) (hm α), rfl⟩
  · intro f hf
    exact ⟨Submodule.mem_sup_right hf, spaceP_le_filTop X s hf⟩

theorem filP : FilMono → ∀ (K : Type) [Field K] [NumberField K] (X : Data K) (s : Fin X.D → Fin X.N → K),
    X.IsGood s → IsNef K X.LA → IsBig K X.LA → Fil (X.ideal s) (X.T - X.D) (spaceV X s) = spaceP X s :=
  fun hF K _ _ X s hs hn hb => fil_spaceV_eq_spaceP hF K X s hs hn hb

end GlobalTheory.HSCore
end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKDef

theorem DPair.form_law {p : ℕ} [Fact p.Prime] (G : HTGroup p) (P : DPair G) (v : InfinitePlace G.F) :
    (G.psi v P.γ)ᴴ * (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) * G.psi v P.γ =
      ((P.c : ℚ) : ℂ) • (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) := by
  have hgu : IsUnit (G.gram v).det := isUnit_iff_ne_zero.mpr (G.gram_det v)
  have hgg : G.gram v * (G.gram v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hgu
  have hgg' : (G.gram v)⁻¹ * G.gram v = 1 := Matrix.nonsing_inv_mul _ hgu
  have hH : ∀ x : G.C, (G.psi v x)ᴴ = G.gram v * G.psi v (sh G x) * (G.gram v)⁻¹ := by
    intro x
    have e : G.psi v (sh G x) = (G.gram v)⁻¹ * (G.psi v x)ᴴ * G.gram v := G.psi_star v x
    rw [e, ← mul_assoc, ← mul_assoc, hgg, one_mul, mul_assoc, hgg, mul_one]
  have hu : sh G (P.γ : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * P.γ =
      algebraMap ℚ G.C (P.c : ℚ) * ((P.β⁻¹ : G.Cˣ) : G.C) := by
    apply (Units.mul_right_inj (P.γ * P.β)).mp
    rw [Units.val_mul, ← Algebra.smul_def]
    calc (P.γ : G.C) * P.β * (sh G (P.γ : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * P.γ)
        = ((P.γ : G.C) * P.β * sh G (P.γ : G.C)) * ((P.β⁻¹ : G.Cˣ) : G.C) * P.γ := by
          simp only [mul_assoc]
      _ = (P.c : ℚ) • ((P.β : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * P.γ) := by
          rw [P.sim, ← Algebra.smul_def]; simp only [smul_mul_assoc]
      _ = (P.c : ℚ) • ((P.γ : G.C) * P.β * ((P.β⁻¹ : G.Cˣ) : G.C)) := by
          rw [Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [mul_smul_comm, mul_assoc]
  rw [hH]
  calc G.gram v * G.psi v (sh G (P.γ : G.C)) * (G.gram v)⁻¹ * (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) *
        G.psi v P.γ
      = G.gram v * (G.psi v (sh G (P.γ : G.C)) * ((G.gram v)⁻¹ * G.gram v) *
          G.psi v ((P.β⁻¹ : G.Cˣ) : G.C) * G.psi v P.γ) := by simp only [mul_assoc]
    _ = G.gram v * G.psi v (sh G (P.γ : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * P.γ) := by
        rw [hgg', mul_one, map_mul, map_mul]
    _ = G.gram v * ((P.c : ℚ) • G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) := by
        rw [hu, map_mul, RingHom.map_rat_algebraMap, ← Algebra.smul_def]
    _ = _ := by rw [mul_smul_comm, Rat.cast_smul_eq_qsmul]

end GlobalTheory.LKDef
end
