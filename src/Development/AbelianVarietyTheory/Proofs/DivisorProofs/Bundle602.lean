module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle558
public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle493
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle541
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle261
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle550
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle549
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle491
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNatura
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle557
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.MayerVietorisEqv

theorem a4 : GlobalTheory.EtC.A4 := by
  intro R _ U V E U' V' E' f g f' g' p u v hu hv F hc hc' hU hV hW
  obtain ⟨d, hex, hnat⟩ := GlobalTheory.T.exists_mayerVietoris_connecting_exact R F
  have hwf : pullback.map f g f' g' u v p hu hv ≫ pullback.fst f' g' = pullback.fst f g ≫ u := pullback.lift_fst _ _ _
  have hwg : pullback.map f g f' g' u v p hu hv ≫ pullback.snd f' g' = pullback.snd f g ≫ v := pullback.lift_snd _ _ _
  have cf : ∀ n x, pull R f F n (pull R p F n x) = pull R u F n (pull R f' F n x) := by
    intro n x; rw [← pull_comp, ← pull_comp, hu]
  have cg : ∀ n x, pull R g F n (pull R p F n x) = pull R v F n (pull R g' F n x) := by
    intro n x; rw [← pull_comp, ← pull_comp, hv]
  have cfst : ∀ n x, pull R (pullback.map f g f' g' u v p hu hv) F n (pull R (pullback.fst f' g') F n x) =
      pull R (pullback.fst f g) F n (pull R u F n x) := by
    intro n x; rw [← pull_comp, ← pull_comp, hwf]
  have csnd : ∀ n x, pull R (pullback.map f g f' g' u v p hu hv) F n (pull R (pullback.snd f' g') F n x) =
      pull R (pullback.snd f g) F n (pull R v F n x) := by
    intro n x; rw [← pull_comp, ← pull_comp, hwg]
  have hcond : ∀ n x, pull R (pullback.fst f g) F n (pull R f F n x) =
      pull R (pullback.snd f g) F n (pull R g F n x) := by
    intro n x; rw [← pull_comp, ← pull_comp, pullback.condition]
  intro n
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
  constructor
  · rw [injective_iff_map_eq_zero]
    intro y hy
    have h1 : pull R f' F (m + 1) y = 0 := by
      apply (hU (m + 1)).1
      rw [← cf, hy, map_zero, map_zero]
    have h2 : pull R g' F (m + 1) y = 0 := by
      apply (hV (m + 1)).1
      rw [← cg, hy, map_zero, map_zero]
    obtain ⟨c, rfl⟩ := ((hex f' g' hc' m).2.2 y).1 ⟨h1, h2⟩
    have hd : d f g hc m (pull R (pullback.map f g f' g' u v p hu hv) F m c) = 0 := by
      rw [← hnat f g f' g' p u v hu hv hc hc' m c]; exact hy
    obtain ⟨a, b, hab⟩ := ((hex f g hc m).2.1 _).1 hd
    obtain ⟨a', rfl⟩ := (hU m).2 a
    obtain ⟨b', rfl⟩ := (hV m).2 b
    have hc1 : c = pull R (pullback.fst f' g') F m a' - pull R (pullback.snd f' g') F m b' := by
      apply (hW m).1
      rw [hab, map_sub, cfst, csnd]
    exact ((hex f' g' hc' m).2.1 c).2 ⟨a', b', hc1⟩
  · intro z
    obtain ⟨a', ha'⟩ := (hU (m + 1)).2 (pull R f F (m + 1) z)
    obtain ⟨b', hb'⟩ := (hV (m + 1)).2 (pull R g F (m + 1) z)
    have hab : pull R (pullback.fst f' g') F (m + 1) a' = pull R (pullback.snd f' g') F (m + 1) b' := by
      apply (hW (m + 1)).1
      rw [cfst, csnd, ha', hb', hcond]
    obtain ⟨y, hy1, hy2⟩ := ((hex f' g' hc' (m + 1)).1 a' b').1 hab
    have k1 : pull R f F (m + 1) (z - pull R p F (m + 1) y) = 0 := by
      rw [map_sub, cf, hy1, ha', sub_self]
    have k2 : pull R g F (m + 1) (z - pull R p F (m + 1) y) = 0 := by
      rw [map_sub, cg, hy2, hb', sub_self]
    obtain ⟨c, hc0⟩ := ((hex f g hc m).2.2 _).1 ⟨k1, k2⟩
    obtain ⟨c', rfl⟩ := (hW m).2 c
    refine ⟨y + d f' g' hc' m c', ?_⟩
    rw [map_add (f := _), hnat f g f' g' p u v hu hv hc hc' m c', hc0]
    abel

end GlobalTheory.MayerVietorisEqv
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace

namespace GlobalTheory.AnPer.Charts

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}

theorem le_of_deg_eq {K : Charts F} {m m' : Λ} {a b : K.K} (e : K.le m a b) (hm : m = m') : K.le m' a b :=
  hm ▸ e

theorem ptHom_deg_eq (K : Charts F) {m m' : Λ} {k : K.K} (T : K.Obj) (e : K.le m T.k k) (hm : m = m') :
    ptHom T e = ptHom T (le_of_deg_eq e hm) := by
  subst hm; rfl

theorem ptHom_triv_comp (K : Charts F) {l m : Λ} {k k' : K.K} (e : K.le l k' k) (T : K.Obj)
    (e₂ : K.le m T.k k') : ptHom (K.triv k') e ≫ ptHom T e₂ = ptHom T (K.le_trans e e₂) :=
  hom_ext (fun c ↦ show T.ρ (K.sh e₂ (K.sh e c)) = T.ρ (K.sh (K.le_trans e e₂) c) by rw [sh_sh]) rfl

theorem ptHom_eq_comp (K : Charts F) {m : Λ} {k : K.K} (T : K.Obj) (e : K.le m T.k k) :
    ptHom T e = ptHom (K.triv T.k) e ≫ ptHom T (K.le_refl T.k) :=
  hom_ext (fun c ↦ show T.ρ (K.sh e c) = T.ρ (K.sh (K.le_refl T.k) (K.sh e c)) by rw [sh_refl]) (add_zero m).symm

theorem invCochain_const : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
    (K : Charts F), K.Rich → ∀ (h : C1 K.Oc) (l : Λ),
    (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = l → ψ.deg = 0 →
      h T T'' (φ ≫ ψ) = ψ.φ (h T T' φ)) →
    (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = l →
      h T T'' (φ ≫ ψ) = h T' T'' ψ) →
    ∃ p : Hol F.V, ∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = l → h T T' φ = algebraMap (Hol F.V) T'.C p := by
  intro I _ g Λ _ F K hK h l hA hB

  let B : ∀ k' k : K.K, K.le l k' k → Hol (K.W k') := fun k' k e ↦ h _ _ (ptHom (K.triv k') e)
  have hBv : ∀ {m : Λ} {k k' : K.K} (e : K.le m k' k) (hm : m = l),
      h _ _ (ptHom (K.triv k') e) = B k' k (le_of_deg_eq e hm) := by
    intro m k k' e hm
    rw [ptHom_deg_eq K (K.triv k') e hm]

  have hR : ∀ {k k' k'' : K.K} (e : K.le l k' k) (e₂ : K.le 0 k'' k'),
      K.sh e₂ (B k' k e) = B k'' k (le_of_deg_eq (K.le_trans e e₂) (add_zero l)) := by
    intro k k' k'' e e₂
    have := hA _ _ _ (ptHom (K.triv k') e) (ptHom (K.triv k'') e₂) rfl rfl
    rw [ptHom_triv_comp, hBv _ (add_zero l)] at this
    exact this.symm

  have hC : ∀ {k₀ k k' : K.K} (e₀ : K.le 0 k k₀) (e : K.le l k' k),
      B k' k₀ (le_of_deg_eq (K.le_trans e₀ e) (zero_add l)) = B k' k e := by
    intro k₀ k k' e₀ e
    have := hB _ _ _ (ptHom (K.triv k) e₀) (ptHom (K.triv k') e) rfl rfl
    rw [ptHom_triv_comp, hBv _ (zero_add l)] at this
    exact this

  have hD : ∀ {k k' : K.K} (e : K.le l k' k) (a : Fin g), dw a (B k' k e) = 0 := by
    intro k k' e a
    obtain ⟨χ, hχ, h0, h1, -⟩ := GlobalTheory.T.exists_jet_morphism_extending_translation K e
    have e0 := hB _ _ _ (jet0 k) χ rfl hχ
    have e1 := hB _ _ _ (jet1 k) χ rfl hχ
    rw [h0, hA _ _ _ (ptHom (K.triv k') e) (jet0 k') rfl rfl] at e0
    rw [h1, hA _ _ _ (ptHom (K.triv k') e) (jet1 k') rfl rfl] at e1
    have := congrArg (fun x : TrivSqZeroExt (Hol (K.W k')) (Fin g → Hol (K.W k')) ↦ x.snd a) (e0.trans e1.symm)
    have s0 : ∀ x : Hol (K.W k'), ((jet0 k').φ x : TrivSqZeroExt (Hol (K.W k')) (Fin g → Hol (K.W k'))).snd a = 0 :=
      fun x ↦ by
        show (TrivSqZeroExt.inl (K.sh (K.le_refl k') x) : TrivSqZeroExt (Hol (K.W k')) (Fin g → Hol (K.W k'))).snd a = 0
        rw [TrivSqZeroExt.snd_inl]; rfl
    have s1 : ∀ x : Hol (K.W k'), ((jet1 k').φ x : TrivSqZeroExt (Hol (K.W k')) (Fin g → Hol (K.W k'))).snd a = dw a x :=
      fun x ↦ snd_tszeSec _ x a
    simp only at this
    rw [s0, s1] at this
    exact this.symm

  let K' : Charts F :=
    { K := {x : K.K × K.K // K.le l x.1 x.2}
      W := fun x ↦ K.W x.1.1
      base := fun x ↦ K.base x.1.1
      le := fun m x y ↦ K.le m x.1.1 y.1.1 ∧ K.le m x.1.2 y.1.2
      le_refl := fun x ↦ ⟨K.le_refl _, K.le_refl _⟩
      le_trans := fun h h' ↦ ⟨K.le_trans h.1 h'.1, K.le_trans h.2 h'.2⟩
      maps := fun h ↦ K.maps h.1 }
  have hK' : K'.Rich := by
    refine ⟨fun q hq ↦ ?_, fun m x y q hq hq' ↦ ?_⟩
    · obtain ⟨k₀, h₀⟩ := hK.1 q hq
      obtain ⟨k₂, h₂⟩ := hK.1 (F.shift l q) hq
      obtain ⟨k₃, h₃, -, e₃⟩ := hK.2 l k₀ k₂ q h₀ h₂
      exact ⟨⟨(k₃, k₂), e₃⟩, h₃⟩
    · obtain ⟨⟨k₁', k₁⟩, e₁⟩ := x
      obtain ⟨⟨k₂', k₂⟩, e₂⟩ := y
      change q ∈ K.W k₁' at hq
      change F.shift m q ∈ K.W k₂' at hq'
      have p1 : F.shift l q ∈ K.W k₁ := K.maps e₁ q hq
      have p2 : F.shift m (F.shift l q) ∈ K.W k₂ := by
        rw [← F.shift_add, add_comm, F.shift_add]; exact K.maps e₂ _ hq'
      obtain ⟨k, hk, f₀, fm⟩ := hK.2 m k₁ k₂ _ p1 p2
      obtain ⟨k₅, h₅, g₀, gm⟩ := hK.2 m k₁' k₂' q hq hq'
      obtain ⟨k', hk', j₀, jl⟩ := hK.2 l k₅ k q h₅ hk
      exact ⟨⟨(k', k), jl⟩, hk', ⟨le_of_deg_eq (K.le_trans g₀ j₀) (add_zero 0), f₀⟩,
        ⟨le_of_deg_eq (K.le_trans gm j₀) (add_zero m), fm⟩⟩
  obtain ⟨p, hp⟩ := GlobalTheory.AnPer.Charts.exists_cst_of_dw_eq_zero K' hK' (fun x ↦ B x.1.1 x.1.2 x.2)
    (fun x y e ↦ by
      show K.sh e.1 (B _ _ x.2) = B _ _ y.2
      rw [hR x.2 e.1]
      exact hC e.2 y.2)
    (fun x i ↦ hD x.2 i)
  have hp' : ∀ (k' k : K.K) (e : K.le l k' k), B k' k e = K.cst k' p := fun k' k e ↦ hp ⟨(k', k), e⟩

  have hPt : ∀ {m : Λ} {k : K.K} (T' : K.Obj) (e : K.le m T'.k k), m = l →
      h _ _ (ptHom T' e) = algebraMap (Hol F.V) T'.C p := by
    intro m k T' e hm
    have s4 := hA _ _ _ (ptHom (K.triv T'.k) e) (ptHom T' (K.le_refl T'.k)) hm rfl
    rw [← ptHom_eq_comp, hBv e hm, hp'] at s4
    rw [s4]
    show T'.ρ (K.sh (K.le_refl T'.k) (K.cst T'.k p)) = _
    rw [sh_cst, T'.ρ_cst]
  refine ⟨p, fun T T' φ hφ ↦ ?_⟩
  have hd : (ptHom T (K.le_refl T.k) ≫ φ).deg = l := by
    show 0 + φ.deg = l
    rw [zero_add, hφ]
  have s1 := hB _ _ _ (ptHom T (K.le_refl T.k)) φ rfl hφ
  have s2 := GlobalTheory.T.cochain_eq_of_same_degree_chartMorphism K h l
    (fun k T χ hχ ↦ (hB _ _ _ (jet0 k) χ rfl hχ).trans (hB _ _ _ (jet1 k) χ rfl hχ).symm) _ T'
    (ptHom T (K.le_refl T.k) ≫ φ) hd
  rw [← s1, s2]
  exact hPt T' _ hd

end GlobalTheory.AnPer.Charts
end
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog

theorem lift_topNil {p : ℕ} [Fact p.Prime] {O B Q : Type} [CommRing O] [CommRing B] [CommRing Q]
    [Algebra B Q] {θ : B →+* O} (hF : IsFrame p Q θ) {G : PDivGroup p O} {d : ℕ} (c : Chart G d)
    (t : G.Tate) (n : ℕ) (z : Fin d → B) (hz : ∀ i, θ (z i) = t.pt n (c.x n i)) :
    ∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N := by
  intro i
  obtain ⟨N, a, ha⟩ := c.nil n i
  obtain ⟨a', ha'⟩ := hF.surj (t.pt n a)
  have hw : θ (z i ^ N - p * a') = 0 := by
    rw [map_sub, map_pow, hz, map_mul, map_natCast, ha', ← map_pow, ha, map_mul, map_natCast, sub_self]
  obtain ⟨w, -, hw'⟩ := hF.pd _ hw
  refine ⟨N * p, ?_⟩
  have h1 : (p : B) * a' ∣ (z i ^ N) ^ p - (z i ^ N - p * a') ^ p := by
    have := sub_dvd_pow_sub_pow (z i ^ N) (z i ^ N - p * a') p
    simpa using this
  rw [pow_mul]
  have h2 : (p : B) ∣ (z i ^ N) ^ p - (z i ^ N - p * a') ^ p := dvd_trans (dvd_mul_right _ _) h1
  have h3 : (p : B) ∣ (z i ^ N - p * a') ^ p := hw' ▸ dvd_mul_right _ _
  have := dvd_add h2 h3
  simpa using this

end GlobalTheory.QLog

namespace GlobalTheory.QLog

theorem val_integral {p : ℕ} {σ B Q : Type} [Fintype σ] [DecidableEq σ] [CommRing B] [CommRing Q]
    [Algebra B Q] (z : σ → B) (s : MvPowerSeries σ B) (q : Q)
    (h : HasVal p z (map (algebraMap B Q) s) q) : ∃ b : B, q = algebraMap B Q b := by
  obtain ⟨N, hN⟩ := h 0
  obtain ⟨b, hb⟩ := hN N le_rfl
  have hE : (MvPolynomial.eval fun i => algebraMap B Q (z i))
      (trunc' Q (Finsupp.equivFunOnFinite.symm fun _ => N) (map (algebraMap B Q) s)) =
      algebraMap B Q (MvPolynomial.eval z (trunc' B (Finsupp.equivFunOnFinite.symm fun _ => N) s)) := by
    rw [trunc'_map, MvPolynomial.eval_map, MvPolynomial.eval, MvPolynomial.coe_eval₂Hom,
      MvPolynomial.eval₂_comp_left]
    rfl
  refine ⟨MvPolynomial.eval z (trunc' B (Finsupp.equivFunOnFinite.symm fun _ => N) s) + b, ?_⟩
  rw [hE, pow_zero, one_mul, sub_eq_iff_eq_add'] at hb
  rw [hb, map_add (f := _)]

end GlobalTheory.QLog

namespace GlobalTheory.QLog

theorem hasPeriod_add_smul {p : ℕ} [Fact p.Prime] {O B Q : Type} [CommRing O] [CommRing B]
    [CommRing Q] [Algebra B Q] {θ : B →+* O} (hF : IsFrame p Q θ) {G : PDivGroup p O} {d : ℕ}
    (c : Chart G d) (t : G.Tate) {f g : MvPowerSeries (Fin d) Q} {y y' : B} (b : B)
    (hf : c.HasPeriod θ t f y) (hg : c.HasPeriod θ t g y') :
    c.HasPeriod θ t (f + algebraMap B Q b • g) (y + b * y') := by
  rw [c.hasPeriod_iff hF] at hf hg ⊢
  intro n z hz
  obtain ⟨q, hq, b1, hb1⟩ := hf n z hz
  obtain ⟨r, hr, b2, hb2⟩ := hg n z hz
  have h1 := (GlobalTheory.QLog.ValLin.hasVal_add_smul_map p B O Q θ hF (Fin d) z g g r r hr).2.1 (algebraMap B Q b)
  have h2 := (GlobalTheory.QLog.ValLin.hasVal_add_smul_map p B O Q θ hF (Fin d) z _ _ q _ hq).1 h1
  refine ⟨_, h2, b1 + b * b2, ?_⟩
  have e : (p : Q) ^ n * (q + algebraMap B Q b * r) =
      (p : Q) ^ n * q + algebraMap B Q b * ((p : Q) ^ n * r) := by ring
  rw [e, hb1, hb2, ← map_mul, ← map_add (f := _)]
  congr 1
  ring

theorem hasPeriod_integral {p : ℕ} [Fact p.Prime] {O B Q : Type} [CommRing O] [CommRing B]
    [CommRing Q] [Algebra B Q] {θ : B →+* O} (hF : IsFrame p Q θ) {G : PDivGroup p O} {d : ℕ}
    (c : Chart G d) (t : G.Tate) (s : MvPowerSeries (Fin d) B) :
    c.HasPeriod θ t (map (algebraMap B Q) s) 0 := by
  rw [c.hasPeriod_iff hF]
  intro n z hz
  have hD : DIn (⊤ : Ideal B) (map (algebraMap B Q) s) := fun α i =>
    ⟨(α i : B) * coeff α s, trivial, by rw [coeff_map, map_mul, map_natCast]⟩
  obtain ⟨q, hq, -⟩ := GlobalTheory.QLog.existsUnique_hasVal_of_dIn p B O Q θ hF (Fin d) z (lift_topNil hF c t n z hz) _ hD
  obtain ⟨e, he⟩ := val_integral z s q hq
  exact ⟨q, hq, e, by rw [he, zero_add, map_mul, map_pow, map_natCast]⟩

open MvPowerSeries in
private lemma exists_pow_dvd_of_theta_eq_of_isFrame {p : ℕ} {B O Q : Type} [CommRing B] [CommRing Q]
    [CommRing O] [Algebra B Q] {θ : B →+* O} (hθ : _root_.GlobalTheory.QLog.IsFrame p Q θ)
    {z : B} {a : O} (hza : θ z = a) {N : ℕ} (ha : (p : O) ∣ a ^ N) :
    ∃ M, (p : B) ∣ z ^ M := by
  obtain ⟨w, hw⟩ := ha
  obtain ⟨b, hb⟩ := hθ.surj w
  obtain ⟨y, -, hy⟩ := hθ.pd (z ^ N - p * b)
    (by simp [hza, hb, hw])
  refine ⟨N * p, ?_⟩
  have h1 : (p : B) ∣ (z ^ N) ^ p - (z ^ N - p * b) ^ p :=
    (dvd_mul_right (p : B) b).trans (by simpa using sub_dvd_pow_sub_pow (z ^ N) (z ^ N - p * b) p)
  have h2 : (z ^ N) ^ p = ((z ^ N) ^ p - (z ^ N - p * b) ^ p) + p * y := by rw [← hy]; ring
  rw [pow_mul, h2]
  exact dvd_add h1 (dvd_mul_right _ _)

open MvPowerSeries in
private lemma eval_algebraMap_trunc'_map_eq_algebraMap_eval {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q]
    {d : ℕ} (s : MvPowerSeries (Fin d) B) (z : Fin d → B) (N : ℕ) :
    MvPolynomial.eval (fun i ↦ algebraMap B Q (z i))
        (trunc' Q (Finsupp.equivFunOnFinite.symm fun _ ↦ N) (map (algebraMap B Q) s)) =
      algebraMap B Q (MvPolynomial.eval z (trunc' B (Finsupp.equivFunOnFinite.symm fun _ ↦ N) s)) := by
  rw [MvPowerSeries.trunc'_map, MvPolynomial.eval_map, MvPolynomial.eval, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.eval₂_comp_left, RingHom.comp_id]
  rfl


open MvPowerSeries in
theorem _root_.GlobalTheory.QLog.hasPeriod_linear : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : _root_.GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.IsPrimitiveSystem ε), ∀ F : _root_.GlobalTheory.QLog.BFrame ε, ∀ (G : _root_.GlobalTheory.PDivGroup p O) (d : ℕ) (c : _root_.GlobalTheory.QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), _root_.GlobalTheory.QLog.IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (f g : MvPowerSeries (Fin d) F.Q) (t : G.Tate) (y y' b : F.B), c.HasPeriod F.θ t f y → c.HasPeriod F.θ t g y' → c.HasPeriod F.θ t (f + algebraMap F.B F.Q b • g) (y + b * y') ∧ (∀ s : MvPowerSeries (Fin d) F.B, constantCoeff s = 0 → c.HasPeriod F.θ t (map (algebraMap F.B F.Q) s) 0) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ ε _ F G d c μ' _ _ f g t y y' b hf hg
  have hF := F.frame
  rw [c.hasPeriod_iff hF] at hf hg
  refine ⟨?_, ?_⟩
  · rw [c.hasPeriod_iff hF]
    intro n z hz
    obtain ⟨q, hq, b₁, hb₁⟩ := hf n z hz
    obtain ⟨r, hr, b₂, hb₂⟩ := hg n z hz
    have hbr := (_root_.GlobalTheory.QLog.ValLin.hasVal_add_smul_map p _ O _ F.θ hF (Fin d) z g f
      r q hr).2.1 (algebraMap _ _ b)
    refine ⟨q + algebraMap _ _ b * r,
      (_root_.GlobalTheory.QLog.ValLin.hasVal_add_smul_map p _ O _ F.θ hF (Fin d) z f _ q _
        hq).1 hbr, b₁ + b * b₂, ?_⟩
    simp only [map_add (f := _), map_mul, map_pow, map_natCast] at hb₁ hb₂ ⊢
    linear_combination hb₁ + algebraMap _ _ b * hb₂
  · intro s _
    rw [c.hasPeriod_iff hF]
    intro n z hz
    have hz' : ∀ i, ∃ M, (p : F.B) ∣ z i ^ M := fun i => by
      obtain ⟨N, hN⟩ := c.nil n i
      refine exists_pow_dvd_of_theta_eq_of_isFrame hF (hz i) (N := N) ?_
      simpa [map_pow, map_natCast] using map_dvd (t.pt n) hN
    have hd : _root_.GlobalTheory.QLog.DIn (⊤ : Ideal F.B)
        (map (algebraMap F.B F.Q) s) := by
      intro α i
      exact ⟨(α i : F.B) * coeff α s, Submodule.mem_top, by simp⟩
    obtain ⟨q, hq, -⟩ := _root_.GlobalTheory.QLog.existsUnique_hasVal_of_dIn p _ O _
      F.θ hF (Fin d) z hz' _ hd
    have hq' := hq
    unfold _root_.GlobalTheory.QLog.HasVal at hq'
    obtain ⟨N, hN⟩ := hq' 0
    obtain ⟨e, he⟩ := hN N le_rfl
    refine ⟨q, hq, MvPolynomial.eval z
      (trunc' F.B (Finsupp.equivFunOnFinite.symm fun _ ↦ N) s) + e, ?_⟩
    rw [eval_algebraMap_trunc'_map_eq_algebraMap_eval, pow_zero, one_mul] at he
    have hq2 : q = algebraMap _ F.Q (MvPolynomial.eval z
        (trunc' F.B (Finsupp.equivFunOnFinite.symm fun _ ↦ N) s) + e) := by
      rw [map_add (f := _), ← he]
      ring
    rw [hq2, zero_add, map_mul, map_pow, map_natCast]

end GlobalTheory.QLog
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.EvRes

theorem comp_eval_eq {σ O A A' : Type} [Fintype σ] [CommRing O] [CommRing A] [CommRing A']
    [Algebra O A] [Algebra O A'] (p : ℕ) [IsHausdorff (Ideal.span {(p : A')}) A']
    (g : A →ₐ[O] A') (x : σ → A) (E : MvPowerSeries σ O →ₐ[O] A) (hE : IsEval p x E)
    (ψ : MvPowerSeries σ O →+* A') (hC : ∀ c, ψ (C c) = algebraMap O A' c)
    (hX : ∀ i, ψ (X i) = g (x i))
    (hψ : ∀ m : ℕ, ∃ N : ℕ, ∀ f, (∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0) → (p : A') ^ m ∣ ψ f)
    (f : MvPowerSeries σ O) : g (E f) = ψ f :=
  CEval.ext_of_cont p ((g : A →+* A').comp (E : MvPowerSeries σ O →+* A)) ψ
    (fun c => by
      show g (E (C c)) = ψ (C c)
      rw [hC, c_eq_algebraMap, AlgHom.commutes, AlgHom.commutes])
    (fun i => by
      show g (E (X i)) = ψ (X i)
      rw [hX, hE.1])
    (fun m => by
      obtain ⟨N, hN⟩ := hE.2 m
      exact ⟨N, fun f hf => by
        show (p : A') ^ m ∣ g (E f)
        have := map_dvd g (hN f hf)
        rwa [map_pow, map_natCast] at this⟩)
    hψ f

theorem constantCoeff_cont {σ O : Type} [CommRing O] (p : ℕ) :
    ∀ m : ℕ, ∃ N : ℕ, ∀ f : MvPowerSeries σ O, (∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0) →
      (p : O) ^ m ∣ constantCoeff f := fun _ =>
  ⟨1, fun f hf => by
    rw [← coeff_zero_eq_constantCoeff_apply, hf 0 (by simp)]
    exact dvd_zero _⟩

end GlobalTheory.EvRes


open GlobalTheory.EvRes in
theorem GlobalTheory.QLog.Chart.ev_res_counit : ∀ (p : ℕ) (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ n, (∀ f, G.res n (c.ev (n + 1) f) = c.ev n f ∧ Coalgebra.counit (R := O) (c.ev n f) = constantCoeff f) ∧ ∀ s, Algebra.TensorProduct.lift (Bialgebra.counitAlgHom O (G.A n)) (Bialgebra.counitAlgHom O (G.A n)) (fun _ _ => Commute.all _ _) (c.ev₂ n s) = constantCoeff s := by
  intro p O _ _ G d c n
  haveI : IsAdicComplete (Ideal.span {(p : G.A n)}) (G.A n) :=
    FinProjComplete.isAdicComplete_of_finite_projective p O (G.A n)
  refine ⟨fun f => ⟨?_, ?_⟩, fun s => ?_⟩
  · exact comp_eval_eq p (G.res n : G.A (n + 1) →ₐ[O] G.A n) (c.x (n + 1)) (c.ev (n + 1))
      (c.isEval (n + 1)) (c.ev n : MvPowerSeries (Fin d) O →+* G.A n)
      (fun a => by rw [c_eq_algebraMap]; exact (c.ev n).commutes a)
      (fun i => by
        show c.ev n (X i) = G.res n (c.x (n + 1) i)
        rw [(c.isEval n).1, c.res])
      (c.isEval n).2 f
  · exact comp_eval_eq p (Bialgebra.counitAlgHom O (G.A n)) (c.x n) (c.ev n) (c.isEval n)
      constantCoeff (fun a => by rw [constantCoeff_C]; rfl)
      (fun i => by
        rw [constantCoeff_X]
        exact (c.aug n i).symm)
      (constantCoeff_cont p) f
  · exact comp_eval_eq p _ _ (c.ev₂ n) (c.isEval₂ n) constantCoeff
      (fun a => by rw [constantCoeff_C]; rfl)
      (fun i => by
        rw [constantCoeff_X]
        rcases i with i | i <;> simp [Bialgebra.counitAlgHom_apply, c.aug n i])
      (constantCoeff_cont p) s
end
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.map_eval_eq_evA_map_of_isEval_of_pow_eq_zero : ∀ (p m : ℕ) (O A k A' σ : Type) [CommRing O] [CommRing A] [Algebra O A] [CommRing k] [CommRing A'] [Algebra k A'] [Fintype σ] (x : σ → A) (E : MvPowerSeries σ O →ₐ[O] A), IsEval p x E → ∀ (r : O →+* k) (g : A →+* A'), (∀ c, g (algebraMap O A c) = algebraMap k A' (r c)) → (p : A') ^ m = 0 → ∀ hx : ∀ i, IsNilpotent (g (x i)), ∀ f, g (E f) = evA k (fun i => g (x i)) hx (map r f) := by
  first | exact @GlobalTheory.algHom_eval_comp_eq_evA_map | exact GlobalTheory.algHom_eval_comp_eq_evA_map | (intros; apply GlobalTheory.algHom_eval_comp_eq_evA_map <;> assumption)
end
