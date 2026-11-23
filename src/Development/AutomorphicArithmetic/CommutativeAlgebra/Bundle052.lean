module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2638
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle853
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1554
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2676
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2239
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1555
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2238
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open UpperTheory.Gal.Int.Geo

namespace UpperTheory.Gal.Int.Geo.QCompPf

variable {q : ℕ} [Fact q.Prime] {D : Datum q} {R R' : Type} [CommRing R] [CommRing R'] [Algebra ℚ R']
  {b : Base D R} {gb : GBase D.toG R'} {N N₀ c : ℕ} {X X' X₁ X₂ : Scheme.{0}} {s : X ⟶ Sp R'}
  {s' : X' ⟶ Sp R'} {s₁ : X₁ ⟶ Sp R} {s₂ : X₂ ⟶ Sp R} {o : GObj gb N s} {o' : GObj gb N s'}
  {u₁ : Obj b N₀ s₁} {u₂ : Obj b N₀ s₂} {f : X ⟶ X₁} {g : X₁ ⟶ X₂} {e : X' ⟶ X}

private def after (n : QMap o u₁ f c) (m : ObjMap u₁ u₂ g) : QMap o u₂ (f ≫ g) c where
  φ := n.φ ≫ m.φ
  φ₂ := n.φ₂ ≫ m.φ₂
  cart := n.cart.comp m.cart
  sq := MapComp.isSquare_comp n.sq m.sq
  act x := by
    have h₁ := n.act x
    have h₂ := m.act x
    simp only [← Category.assoc, h₁]
    simp only [Category.assoc, h₂]
  pol := (n.pol).trans o.isLB (pull_isLB u₁.isLB _) (pull_isLB u₂.isLB _)
    (MapComp.lbIso_pull_comp m.pol n.φ₂ rfl)
  eta y := by
    have h₁ := n.eta y
    have h₂ := m.eta y
    simp only [← Category.assoc, h₁]
    simp only [Category.assoc, h₂]

private def before (m : GObjMap o' o e) (n : QMap o u₁ f c) : QMap o' u₁ (e ≫ f) c where
  φ := m.φ ≫ n.φ
  φ₂ := m.φ₂ ≫ n.φ₂
  cart := m.cart.comp n.cart
  sq := MapComp.isSquare_comp m.sq n.sq
  act x := by
    have h₁ := m.act x
    have h₂ := n.act x
    simp only [← Category.assoc, h₁]
    simp only [Category.assoc, h₂]
  pol := (m.pol).trans o'.isLB (pull_isLB o.isLB _) (pull_isLB u₁.isLB _)
    (MapComp.lbIso_pull_comp n.pol m.φ₂ rfl)
  eta y := by
    have h₁ := m.eta (c • y)
    have h₂ := n.eta y
    simp only [← Category.assoc, h₁]
    simp only [Category.assoc, h₂]

private theorem factor (n' : QMap o u₂ (f ≫ g) c) (m : ObjMap u₁ u₂ g) :
    ∃ n : QMap o u₁ f c, n'.φ = n.φ ≫ m.φ := by
  have hw : n'.φ ≫ u₂.A.hom = (o.A.hom ≫ f) ≫ g := by
    rw [n'.cart.1.w, Category.assoc]
  let ℓ : o.A.left ⟶ u₁.A.left := m.cart.1.lift n'.φ (o.A.hom ≫ f) hw
  have hℓφ : ℓ ≫ m.φ = n'.φ := m.cart.1.lift_fst _ _ _
  have hℓs : ℓ ≫ u₁.A.hom = o.A.hom ≫ f := m.cart.1.lift_snd _ _ _
  obtain ⟨ℓ₂, hsq⟩ := MapComp.exists_isSquare (G := u₁.A) (G' := o.A) hℓs
  have hsq₂ : ℓ₂ ≫ m.φ₂ = n'.φ₂ := by
    apply MapComp.isSquare_unique (MapComp.isSquare_comp hsq m.sq)
    rw [hℓφ]
    exact n'.sq
  refine ⟨⟨ℓ, ℓ₂, ?_, hsq, ?_, ?_, ?_⟩, hℓφ.symm⟩
  · exact IsGrpPullback.cancel m.cart (IsGrpPullback.congr n'.cart rfl hℓφ.symm) hℓs
  · intro x
    apply m.cart.1.hom_ext
    · rw [Category.assoc, Category.assoc, hℓφ, m.act x, ← Category.assoc, hℓφ]
      exact n'.act x
    · rw [Category.assoc, Category.assoc, hℓs, Over.w, hℓs, ← Category.assoc, Over.w]
  · exact LBIso.trans o.isLB (pull_isLB u₂.isLB _) (pull_isLB u₁.isLB _) n'.pol
      (MapComp.lbIso_pull_comp m.pol ℓ₂ hsq₂.symm).symm
  · intro y
    apply m.cart.1.hom_ext
    · rw [Category.assoc, Category.assoc, hℓφ, n'.eta y, m.eta y, Category.assoc]
    · rw [Category.assoc, Category.assoc, hℓs, ← Category.assoc, Over.w]
      simp [Over.w]

private theorem bridge [IsIso f] (n : QMap o u₁ f c) (n' : QMap o u₂ (f ≫ g) c) :
    ∃ m : ObjMap u₁ u₂ g, n'.φ = n.φ ≫ m.φ := by
  haveI hiso : IsIso n.φ := n.cart.1.isIso_fst_of_isIso
  have hinvw : inv n.φ ≫ o.A.hom = u₁.A.hom ≫ inv f := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, n.cart.1.w, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  have hinv : IsGrpPullback u₁.A o.A (inv f) (inv n.φ) :=
    IsGrpPullback.cancel n.cart
      (IsGrpPullback.congr (GlobalTheory.EndLoc.isGrpPullback_id u₁.A) (by simp) (by simp)) hinvw
  have hcart : IsGrpPullback u₁.A u₂.A g (inv n.φ ≫ n'.φ) :=
    IsGrpPullback.congr (IsGrpPullback.comp hinv n'.cart) (by simp) rfl
  obtain ⟨ψ₂, hψ⟩ := MapComp.exists_isSquare (G := o.A) (G' := u₁.A) hinvw
  have hid : Geo.Tor.IsSquare (𝟙 u₁.A.left) (𝟙 (u₁.A ⊗ u₁.A).left) := by
    constructor <;> simp
  have hψn : ψ₂ ≫ n.φ₂ = 𝟙 _ := by
    apply MapComp.isSquare_unique (MapComp.isSquare_comp hψ n.sq)
    rw [IsIso.inv_hom_id]
    exact hid
  refine ⟨⟨inv n.φ ≫ n'.φ, ψ₂ ≫ n'.φ₂, hcart, MapComp.isSquare_comp hψ n'.sq, ?_, ?_, ?_⟩, ?_⟩
  · intro x
    have hx : Over.Hom.left (u₁.act.act x) ≫ inv n.φ = inv n.φ ≫ Over.Hom.left (o.act.act x) := by
      rw [IsIso.comp_inv_eq, Category.assoc, n.act x, IsIso.inv_hom_id_assoc]
    rw [← Category.assoc, hx, Category.assoc, n'.act x, Category.assoc]
  · exact LBIso.trans u₁.isLB (pull_isLB u₁.isLB _) (pull_isLB u₂.isLB _)
      (GlobalTheory.SiegLower.lbIso_pull_id u₁.isLB)
      (LBIso.trans (pull_isLB u₁.isLB _) (pull_isLB o.isLB _) (pull_isLB u₂.isLB _)
        (MapComp.lbIso_pull_comp n.pol ψ₂ hψn.symm).symm
        (MapComp.lbIso_pull_comp n'.pol ψ₂ rfl))
  · intro y
    have hy : Over.Hom.left (u₁.eta y) = inv f ≫ Over.Hom.left (o.eta (c • y)) ≫ n.φ := by
      rw [n.eta y, IsIso.inv_hom_id_assoc]
    rw [hy]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc, n'.eta y, IsIso.inv_hom_id_assoc]
  · simp

end UpperTheory.Gal.Int.Geo.QCompPf

open UpperTheory.Gal.Int.Geo.QCompPf in
theorem UpperTheory.quotient_map_comp : QComp := by
  intro q _ D R R' _ _ _ b gb N N₀ c X X₁ X₂ s s₁ s₂ o u₁ u₂ f g
  refine ⟨fun n m => ⟨after n m, rfl⟩, fun n' m => factor n' m, fun hf n n' => bridge n n', ?_⟩
  intro X' s' o' e m n
  exact ⟨before m n, rfl⟩
end
end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open scoped TensorProduct

namespace UpperTheory.LatticeTracePullback

private theorem eq_of_geom {T Y Z : Scheme.{0}} (π : Y ⟶ Z) [Etale π] (f g : T ⟶ Y) (h : f ≫ π = g ≫ π)
    (hg : ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Spec (CommRingCat.of k) ⟶ T), t ≫ f = t ≫ g) : f = g := by
  set L := pullback.lift f g h with hL
  set Δ := pullback.diagonal π with hΔ
  have hLf : L ≫ pullback.fst π π = f := by rw [hL]; erw [pullback.lift_fst]
  have hLg : L ≫ pullback.snd π π = g := by rw [hL]; erw [pullback.lift_snd]
  have hΔf : Δ ≫ pullback.fst π π = 𝟙 Y := by rw [hΔ]; erw [pullback.diagonal_fst]
  have hΔg : Δ ≫ pullback.snd π π = 𝟙 Y := by rw [hΔ]; erw [pullback.diagonal_snd]
  have e1 : pullback.fst L Δ ≫ f = pullback.snd L Δ := by
    calc pullback.fst L Δ ≫ f = pullback.fst L Δ ≫ L ≫ pullback.fst π π := by rw [hLf]
      _ = pullback.snd L Δ ≫ Δ ≫ pullback.fst π π := by rw [pullback.condition_assoc]
      _ = pullback.snd L Δ := by rw [hΔf, Category.comp_id]
  have e2 : pullback.fst L Δ ≫ g = pullback.snd L Δ := by
    calc pullback.fst L Δ ≫ g = pullback.fst L Δ ≫ L ≫ pullback.snd π π := by rw [hLg]
      _ = pullback.snd L Δ ≫ Δ ≫ pullback.snd π π := by rw [pullback.condition_assoc]
      _ = pullback.snd L Δ := by rw [hΔg, Category.comp_id]
  have hsurj : Surjective (pullback.fst L Δ) := by
    constructor
    intro x
    let K := AlgebraicClosure (T.residueField x)
    let t : Spec (CommRingCat.of K) ⟶ T :=
      Spec.map (CommRingCat.ofHom (algebraMap (T.residueField x) K)) ≫ T.fromSpecResidueField x
    have ht := hg K t
    have hc : t ≫ L = (t ≫ f) ≫ Δ := by
      apply pullback.hom_ext
      · simp only [Category.assoc, hLf, hΔf, Category.comp_id]
      · simp only [Category.assoc, hLg, hΔg, Category.comp_id]
        simpa only [Category.assoc] using ht.symm
    let q : Spec (CommRingCat.of K) ⟶ pullback L Δ := pullback.lift t (t ≫ f) hc
    let pt : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K
    refine ⟨q pt, ?_⟩
    have hq : q ≫ pullback.fst L Δ = t := pullback.lift_fst _ _ _
    have h1 : (pullback.fst L Δ) (q pt) = t pt := by
      rw [← Scheme.Hom.comp_apply, hq]
    rw [h1]
    have h2 : t pt ∈ Set.range (T.fromSpecResidueField x) :=
      ⟨_, (Scheme.Hom.comp_apply _ _ pt).symm⟩
    rwa [Scheme.range_fromSpecResidueField, Set.mem_singleton_iff] at h2
  haveI : IsIso (pullback.fst L Δ) :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, hsurj⟩
  exact (cancel_epi (pullback.fst L Δ)).1 (e1.trans e2.symm)

private theorem lat_step {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (h : G.GAf)
    {c d : ℕ} (hd0 : 0 < d) (hd : d.Coprime p) (hlat : ∀ v ∈ LaHat D, ∃ v' ∈ LaHat D, L.actG h v' = c • v)
    (x : D.La) (hx : ∃ v ∈ LaHat D, L.actG h (inAf D x) = inAf D 0 + d • v) : ∃ u : D.La, c • x = d • u := by
  obtain ⟨v, hv, hxv⟩ := hx
  obtain ⟨v', hv', hv'eq⟩ := hlat v hv
  have hin : ∀ (k : ℕ) (y : D.La), inAf D (k • y) = k • inAf D y := by
    intro k y
    have h1 := map_nsmul (TensorProduct.mk ℤ ℚ D.La 1) k y
    have h2 := map_nsmul (TensorProduct.mk ℚ (AfP p) (VQ D) 1) k ((1 : ℚ) ⊗ₜ[ℤ] y)
    simp only [TensorProduct.mk_apply] at h1 h2
    simp only [inAf, h1, h2]
  have h0 : inAf D 0 = 0 := by simp [inAf]
  rw [h0, zero_add] at hxv
  have hinv : ∀ w, L.actG h⁻¹ (L.actG h w) = w := by
    intro w
    show (L.actG h⁻¹ * L.actG h) w = w
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  have key : inAf D (c • x) = d • v' := by
    have e1 : L.actG h (inAf D (c • x)) = L.actG h (d • v') := by
      rw [hin, map_nsmul, map_nsmul, hxv, hv'eq, smul_comm]
    have e2 := congrArg (L.actG h⁻¹) e1
    rwa [hinv, hinv] at e2
  exact GlobalTheory.T.exists_latticeVector_eq_nsmul_of_adelic_nsmul p D d hd0 hd (GlobalTheory.T.int_dvd_of_eq_nat_mul_integralAdeleAwayFromP p d hd0 hd) (c • x) ⟨v', hv', key⟩

end UpperTheory.LatticeTracePullback

open GlobalTheory.UPel.HT.SiegFactor in
theorem UpperTheory.trace_pullback_identity : TrBack := by
  intro p _ D G L R _ _ gb h X s N' N o' o ψ hT c hc hlat
  obtain ⟨hψ, hcomm, ⟨ψ', d, hψ'm, hcomm', hψψ', hψ'ψ, hd⟩, _, hgeom⟩ := hT
  have hpos : ∀ m : ℕ, m.Coprime p → 0 < m := by
    intro m hm
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0
      rw [Nat.coprime_zero_left] at hm
      exact absurd hm (Fact.out : p.Prime).one_lt.ne'
    · exact h0
  have hd0 := hpos d hd
  have hc0 := hpos c hc
  haveI : IsMonHom (𝟙 o'.A ^ c) := (isMonHom_epi_id_pow o'.A o'.ab hc0).1
  haveI : IsMonHom (𝟙 o.A ^ d) := (isMonHom_epi_id_pow o.A o.ab hd0).1
  haveI : Epi (𝟙 o.A ^ d) := (isMonHom_epi_id_pow o.A o.ab hd0).2
  haveI : Epi (𝟙 o'.A ^ d) := (isMonHom_epi_id_pow o'.A o'.ab hd0).2
  haveI := hψ'm
  haveI := hψ
  have ker : ∀ (T' : Over X) (y : T' ⟶ o'.A), y ≫ ψ = 1 → y ^ c = 1 := by
    intro T' y hy
    have hyd : y ^ d = 1 := by
      rw [← comp_id_pow, ← hψψ', ← Category.assoc, hy, MonObj.one_comp]
    have hunit : IsUnit ((d : ℕ) : Γ(X, ⊤)) := by
      have h1 : IsUnit ((d : ℕ) : R) := by
        have : IsUnit ((d : ℕ) : ℚ) := (Nat.cast_ne_zero.mpr hd0.ne').isUnit
        simpa using this.map (algebraMap ℚ R)
      have h2 := (h1.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).map s.appTop.hom
      simpa using h2
    haveI het : Etale (Over.Hom.left (mulN o'.A d)) :=
      ((GlobalTheory.GrpTangent.finiteEtale_mulN_torsion o'.A (hG := o'.ab) hunit).1).2
    apply Over.OverMorphism.ext
    refine UpperTheory.LatticeTracePullback.eq_of_geom (Over.Hom.left (mulN o'.A d)) _ _ ?_ ?_
    · rw [← Over.comp_left, ← Over.comp_left, GlobalTheory.MulFlatSurj.mulN_eq_pow, comp_id_pow,
        comp_id_pow, ← pow_mul, mul_comm, pow_mul, hyd, one_pow, one_pow]
    · intro k _ _ t
      obtain ⟨φ, hφ⟩ := Spec.map_surjective ((t ≫ T'.hom) ≫ s)
      obtain ⟨I', I'', -, -, hiff⟩ := hgeom k (t ≫ T'.hom) φ.hom (by rw [← hφ]; rfl)
      let u : Over.mk (t ≫ T'.hom) ⟶ T' := Over.homMk t rfl
      have hz : (u ≫ y) ^ d = 1 := by rw [← MonObj.comp_pow, hyd, MonObj.comp_one]
      obtain ⟨a, ha⟩ := (I'.onto d hd0 (u ≫ y)).1 hz
      have h0'' : I''.ev d 0 = 1 := by
        have := I''.add d 0 0
        rw [add_zero] at this
        exact mul_eq_left.mp this.symm
      have h0' : I'.ev d 0 = 1 := by
        have := I'.add d 0 0
        rw [add_zero] at this
        exact mul_eq_left.mp this.symm
      have hx := (hiff d hd0 hd a 0).1 (by rw [ha, Category.assoc, hy, MonObj.comp_one]; exact h0''.symm)
      obtain ⟨w, hw⟩ := UpperTheory.LatticeTracePullback.lat_step L h hd0 hd hlat a hx
      have hpowev : ∀ m : ℕ, I'.ev d (m • a) = (I'.ev d a) ^ m := by
        intro m
        induction m with
        | zero => rw [zero_smul, pow_zero, h0']
        | succ m ih => rw [succ_nsmul, I'.add, ih, pow_succ]
      have hk : I'.ev d (c • a) = 1 := (I'.ker d hd0 _).2 ⟨w, hw⟩
      rw [hpowev, ha, ← MonObj.comp_pow] at hk
      have h1 : (1 : Over.mk (t ≫ T'.hom) ⟶ o'.A) = u ≫ 1 := (MonObj.comp_one u).symm
      rw [h1] at hk
      have := congrArg Over.Hom.left hk
      simpa only [Over.comp_left, Over.homMk_left, u] using this
  obtain ⟨hfl, hsu, hqc⟩ := SiegUniqBase.flat_surjective_qc_pow X o.A o.ab d hd0
  obtain ⟨⟨χ, hχm, hχ⟩, _⟩ := GlobalTheory.exists_monHom_factor_of_flat_surjective X o.A o.A o'.A
    (𝟙 o.A ^ d) (ψ' ≫ 𝟙 o'.A ^ c) inferInstance inferInstance hfl hsu hqc (by
      intro T' x hx
      rw [comp_id_pow] at hx
      have hy : (x ≫ ψ') ≫ ψ = 1 := by rw [Category.assoc, hψ'ψ, comp_id_pow, hx]
      rw [← Category.assoc, comp_id_pow]
      exact ker T' _ hy)
  refine ⟨χ, hχm, ?_, ?_⟩
  · apply (cancel_epi (𝟙 o'.A ^ d)).1
    rw [← Category.assoc, id_pow_comp ψ d, Category.assoc, hχ, ← Category.assoc, hψψ']
  · apply (cancel_epi (𝟙 o.A ^ d)).1
    rw [← Category.assoc, hχ, Category.assoc, id_pow_comp ψ c, ← Category.assoc, hψ'ψ]
end
