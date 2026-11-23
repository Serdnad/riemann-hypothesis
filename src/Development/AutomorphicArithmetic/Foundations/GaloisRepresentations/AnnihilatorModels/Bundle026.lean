module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle011
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PairCalc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle510
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharZeroOfIsUnit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1159
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3050
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.etInj_of :
    ObjTri → LevPull → EtInj := by
  intro hTri hPull p _ D R _ b N h3 hc M 𝔞 ρ E π hπ mπ X u v huv hlv
  obtain ⟨o₁, ⟨m₁⟩⟩ := GlobalTheory.T.exists_harrisTaylorObject_pullback p D R b N E.X X E.s u E.univ
  obtain ⟨l, hl, hlu⟩ := hPull p D R b N E.X X E.s (u ≫ E.s) u E.univ o₁ m₁ 𝔞 ρ E.lv E.isLev
  obtain ⟨m₁₃, hm₁₃⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ m₁ mπ
  obtain ⟨m₂, hm₂⟩ := (hTri p D R b N h3 hc X E.X M.X (u ≫ E.s) E.s M.s o₁ E.univ M.univ v π).2
    (u ≫ π) huv.symm m₁₃ mπ
  have hvs : v ≫ E.s = u ≫ E.s := by
    rw [← hπ, ← Category.assoc, ← Category.assoc, huv]
  have hsec : ∀ y, (l y).left ≫ o₁.A.hom = 𝟙 X := fun y => by
    simpa using Over.w (l y)
  have hsec' : ∀ y, (E.lv y).left ≫ E.univ.A.hom = 𝟙 E.X := fun y => by
    simpa using Over.w (E.lv y)
  have hlv₂ : ∀ y, (l y).left ≫ m₂.φ = v ≫ (E.lv y).left := fun y => by
    refine mπ.cart.1.hom_ext ?_ ?_
    · simp only [Category.assoc]
      rw [hm₂, hm₁₃, ← Category.assoc, hlu y, Category.assoc, hlv y]
    · simp only [Category.assoc]
      rw [m₂.cart.1.w, ← Category.assoc, hsec, hsec', Category.comp_id]
      exact Category.id_comp v
  exact (E.rep X _ o₁ l hl).unique ⟨rfl, m₁, hlu⟩ ⟨hvs, m₂, hlv₂⟩
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.tjEEx_of :
    ObjTri → PulledEx → PullKer → UKerW → LevPull → LevPush → TjEEx := by
  intro hTri hPE hPK hUW hLP hLPush p _ D O _ _ _ _ f b N r w _ hS M j c T hF 𝔞 ρ hsup hu E π hπ mπ
  have h3 := hS.three
  have hcop := hS.cop
  obtain ⟨Z, s, g, pb⟩ : ∃ (Z : Scheme.{0}) (s : Z ⟶ E.X) (g : Z ⟶ T.Y), IsPullback s g π T.s :=
    ⟨_, _, _, IsPullback.of_hasPullback π T.s⟩
  obtain ⟨o, ⟨ms⟩⟩ := GlobalTheory.T.exists_harrisTaylorObject_pullback p D O b N E.X Z E.s s E.univ
  obtain ⟨m₁, hm₁⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ ms mπ
  have hx : (s ≫ π) ≫ M.s = s ≫ E.s := by rw [Category.assoc, hπ]
  obtain ⟨P⟩ := hPE p D O b N h3 hcop M r w j c T Z (s ≫ π) (s ≫ E.s) hx o m₁ g pb.w.symm
  obtain ⟨l, hl, hlm⟩ := hLP p D O b N E.X Z E.s (s ≫ E.s) s E.univ o ms 𝔞 ρ E.lv E.isLev
  have hK : ∀ (X : Over Z) (g' : X ⟶ o.A), UKer r o P.ψ X g' → KilledBy o w g' := by
    rintro X g' ⟨h1, e, h2⟩
    let g₀ : (Over.mk (X.hom ≫ g) : Over T.Y) ⟶ T.o.A := Over.homMk (g'.left ≫ P.m₀.φ) (by
      have hw := P.m₀.cart.1.w
      have hg := Over.w g'
      simp only [Category.assoc, hw, Over.mk_hom]
      rw [← Category.assoc, hg])
    obtain ⟨Ha, -, Hc⟩ := (hPK p D O b N T.Y Z (T.s ≫ M.s) (s ≫ E.s) g T.o T.o' o P.o' P.m₀ P.m' T.ψ P.ψ P.sq).1
      X (Over.mk (X.hom ≫ g)) rfl g' g₀ (by simp [g₀])
    exact (Hc w).2 (hUW p D O f b N r w hS M j c T hF _ g₀ ⟨Ha.1 h1, e, (Hc _).1 h2⟩)
  have hl' := hLPush p D O b N r w 𝔞 ρ hsup hu Z (s ≫ E.s) c o P.o' P.ψ P.isog hK l hl
  obtain ⟨t, ⟨ht, mt, hlev⟩, -⟩ := E.rep Z (s ≫ E.s) P.o' _ hl'
  obtain ⟨n₁, hn₁⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ mt mπ
  obtain ⟨n₂, hn₂⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ P.m' T.mt
  have e : t ≫ π = g ≫ T.t := (M.rep Z (s ≫ E.s) P.o').unique
    ⟨by rw [Category.assoc, hπ, ht], ⟨n₁⟩⟩
    ⟨by rw [Category.assoc, ← T.st, ← Category.assoc, ← pb.w, Category.assoc, hπ], ⟨n₂⟩⟩
  have hφ : ∀ (f₁ f₂ : Z ⟶ M.X) (_ : f₁ = f₂) (a : ObjMap P.o' M.univ f₁) (a' : ObjMap P.o' M.univ f₂), a.φ = a'.φ := by
    rintro f₁ _ rfl a a'
    exact (hTri p D O b N h3 hcop Z M.X M.X _ M.s M.s P.o' M.univ M.univ f₁ (𝟙 _)).1 a a'
  refine ⟨{ Z := Z, s := s, t := t, g := g, pb := pb, tπ := e, o := o, o' := P.o', ms := ms, mt := mt, ψ := P.ψ,
            isog := P.isog, tj := P.tj, m₀ := P.m₀, m' := P.m', sq := P.sq, tri := P.tri.trans hm₁,
            tri' := hn₂.symm.trans ((hφ _ _ e.symm n₂ n₁).trans hn₁), lev := ?_ }⟩
  intro y l' hl''
  have hll : l' = l y := by
    apply Over.OverMorphism.ext
    apply ms.cart.1.hom_ext
    · rw [hl'', hlm]
    · rw [Over.w l', Over.w (l y)]
  subst hll
  exact hlev y
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.caseW_of :
    SameW → FrobIsog → IsogComp → KerFromU → IsoOfKer → ImgEq → PulledRead → CaseW := by
  intro hSame hFrob hComp hKer hIso hImg hRead
  intro p _ D O _ _ _ _ f b N r w _ hstd M j j₁ hj T T' κ _ _ _ φ hφ x β hx hβ o₁ m₁ y y' hy hy' P P' hrep hrep' hcard hiff
  subst hj
  have hpp : p.Prime := Fact.out
  have hfinR : Finite (IsLocalRing.ResidueField O) :=
    Nat.finite_of_card_ne_zero (by rw [hstd.card]; exact pow_ne_zero _ hpp.ne_zero)
  have hq : ∀ a : O, β a ^ (p ^ f) = β a := by
    intro a
    letI := Fintype.ofFinite (IsLocalRing.ResidueField O)
    have h1 : (IsLocalRing.residue O a) ^ (p ^ f) = IsLocalRing.residue O a := by
      rw [← hstd.card, Nat.card_eq_fintype_card]
      exact FiniteField.pow_card _
    have h2 : a ^ (p ^ f) - a ∈ IsLocalRing.maximalIdeal O := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, h1, sub_self]
    have h3 := hβ _ h2
    rw [map_sub, map_pow, sub_eq_zero] at h3
    exact h3
  have hfix : spMap φ ≫ spMap β = spMap β := by
    have hc : φ.comp β = β := RingHom.ext fun a => by rw [RingHom.comp_apply, hφ, hq]
    rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hc]
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · exfalso
      have hc := hstd.card
      rw [h0, pow_zero] at hc
      have := Finite.one_lt_card (α := IsLocalRing.ResidueField O)
      omega
    · exact h0
  have hw : w ≠ ⊤ := Ideal.IsMaximal.ne_top ‹_›
  have hβw : ∀ (i : Fin D.a), ∀ z ∈ w, β ((b.t i) z) = 0 := fun i z hz => hβ _ (hstd.tw i z hz)
  obtain ⟨o'', mF, F, hFi, hFa, hFk⟩ := hFrob p D O b N f κ (spMap β) φ hφ hfix P'.o'
  have hcomp := hComp p D O b N (Sp κ) (spMap β) _ _ o₁ P'.o' o'' P'.ψ F P'.isog hFi
  have hexp : p ^ (f * j) * p ^ f = p ^ (f * (j + 1)) := by
    rw [← pow_add]
    ring_nf
  rw [hexp] at hcomp
  have he : f * (j + 1) - 1 + 1 = f * (j + 1) :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.mul_pos hf (Nat.succ_pos j)).ne')
  have hcard1 : Nat.card { g // UKer r o₁ P.ψ (𝟙_ (Over (Sp κ))) g } = (p ^ f) ^ j := by
    rw [← hcard]
    exact Nat.card_congr (Equiv.subtypeEquivRight hiff)
  have hU := hSame p D O b N hstd.m1 hstd.a1 r w hw hstd.ule f κ β hβw o₁ P.o' P'.o' o'' P.ψ P'.ψ F
    (f * (j + 1) - 1) (by rw [he]; exact P.isog) P'.isog.2.1 (by rw [he]; exact hcomp) hFk ((p ^ f) ^ j)
    (pow_pos (pow_pos hpp.pos _) _) (by rw [← pow_succ']; exact hrep) hcard1 hrep' hcard hiff
  have hK1 := hKer p D O b N r w hw hstd.ule κ (spMap β) _ o₁ P.o' o'' P.ψ (P'.ψ ≫ F) P.isog hcomp hU
  have hK2 := hKer p D O b N r w hw hstd.ule κ (spMap β) _ o₁ o'' P.o' (P'.ψ ≫ F) P.ψ hcomp P.isog
    (fun T g => (hU T g).symm)
  obtain ⟨m₂, hm₂⟩ := hIso p D O b N κ (spMap β) _ o₁ P.o' o'' P.ψ (P'.ψ ≫ F) P.isog hcomp
    (fun T g => ⟨hK1 T g, hK2 T g⟩)
  obtain ⟨n₁, hn₁⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ P.m' T.mt
  obtain ⟨n₂a, hn₂a⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ P'.m' T'.mt
  obtain ⟨n₂, hn₂⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ mF n₂a
  have h₁ : (y ≫ T.t) ≫ M.s = spMap β := by
    rw [Category.assoc, ← T.st, ← Category.assoc, hy, hx]
  have h₂ : (spMap φ ≫ y' ≫ T'.t) ≫ M.s = spMap β := by
    simp only [Category.assoc]
    rw [← T'.st, ← Category.assoc y', hy', hx, hfix]
  obtain ⟨ht, hφeq⟩ := hImg p D O b N hstd.three hstd.cop M (Sp κ) (spMap β) P.o' o''
    (y ≫ T.t) (spMap φ ≫ y' ≫ T'.t) h₁ h₂ n₁ n₂ m₂
  refine ⟨ht, ?_⟩
  intro a h h'
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : 𝟙_ (Over (Sp κ)) ⟶ o₁.A, Over.Hom.left a₀ ≫ m₁.φ = a := by
    refine ⟨Over.homMk (m₁.cart.1.lift a (𝟙 _) (by rw [Category.id_comp, h, hy])) ?_, ?_⟩
    · simp
    · simp
  subst ha₀
  rw [(hRead p D O b N M r w (j + 1) _ T (Sp κ) x (spMap β) o₁ m₁ y hy P a₀).2 h,
    (hRead p D O b N M r w j _ T' (Sp κ) x (spMap β) o₁ m₁ y' hy' P' a₀).2 h',
    ← hn₁, ← hφeq, hn₂, hn₂a]
  have key := hFa (a₀ ≫ P'.ψ)
  simp only [Over.comp_left, Category.assoc] at key hm₂ ⊢
  rw [reassoc_of% hm₂, reassoc_of% key]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private theorem isUnit_natCast_of {X Y : Scheme.{0}} (g : X ⟶ Y) {n : ℕ} (h : IsUnit ((n : ℕ) : Γ(Y, ⊤))) :
    IsUnit ((n : ℕ) : Γ(X, ⊤)) := by
  have := h.map g.appTop.hom
  rwa [map_natCast] at this

private theorem exists_id {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    (hT : ObjTri) (hN : 3 ≤ N) (hNp : N.Coprime p) {S S₃ : Scheme.{0}} {s : S ⟶ Sp R} {s₃ : S₃ ⟶ Sp R}
    {o : Obj b N s} {o₃ : Obj b N s₃} {g : S ⟶ S₃} (m : ObjMap o o₃ g) :
    ∃ i : ObjMap o o (𝟙 S), i.φ = 𝟙 _ := by
  obtain ⟨i, hi⟩ := (hT p D R b N hN hNp _ _ _ _ _ _ o o o₃ (𝟙 S) g).2 g (Category.id_comp g) m m
  refine ⟨i, m.cart.1.hom_ext ?_ ?_⟩
  · rw [hi, Category.id_comp]
  · rw [i.cart.1.w, Category.comp_id, Category.id_comp]

private theorem et_of {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    (hT : ObjTri) (hI : PullIsog) (hK : PullKer) (hN : 3 ≤ N) (hNp : N.Coprime p)
    {M : Model b N} {r : ℤ} {w : Ideal (𝓞 D.F)} {j c : ℕ}
    {Y : Scheme.{0}} {s : Y ⟶ M.X} {o o' : Obj b N (s ≫ M.s)} (ms : ObjMap o M.univ s) {ψ : o.A ⟶ o'.A}
    (iso : IsPIsog c o o' ψ) (tj : IsTj r w j o o' ψ) (hY : Univ r w j c M s o o' ψ)
    {Y₀ : Scheme.{0}} {s₀ : Y₀ ⟶ M.X} (gs : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme)
    (hgs : gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀) (egs : Etale gs)
    {o₀ o₀' : Obj b N (s₀ ≫ M.s)} (ms₀ : ObjMap o₀ M.univ s₀) {ψ₀ : o₀.A ⟶ o₀'.A}
    (iso₀ : IsPIsog c o₀ o₀' ψ₀) (tj₀ : IsTj r w j o₀ o₀' ψ₀) (hY₀ : Univ r w j c M s₀ o₀ o₀' ψ₀) :
    Etale (s ∣_ M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))) := by
  have hpU : IsUnit ((p : ℕ) : Γ((M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme, ⊤)) := by
    have h0 := GlobalTheory.EtC.PairDich.isUnit_ι_appTop (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))) ((p : ℕ) : Γ(M.X, ⊤)) le_rfl
    rwa [map_natCast] at h0
  have hp₀ : IsUnit ((p : ℕ) : Γ(Y₀, ⊤)) := isUnit_natCast_of gs hpU
  have hpV : IsUnit ((p : ℕ) : Γ((s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).toScheme, ⊤)) :=
    isUnit_natCast_of (s ∣_ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))) hpU
  have hPB := isPullback_morphismRestrict s (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))
  obtain ⟨oV, ⟨mV⟩⟩ := GlobalTheory.T.exists_harrisTaylorObject_pullback p D R b N M.X (s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).toScheme M.s
    ((s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).ι ≫ s) M.univ
  obtain ⟨mVo, -⟩ := (hT p D R b N hN hNp _ Y M.X _ (s ≫ M.s) M.s oV o M.univ
    (s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).ι s).2 _ rfl mV ms
  obtain ⟨oV', mV', ψV, isoV, sqV⟩ := hI p D R b N Y (s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).toScheme
    (s ≫ M.s) _ (s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).ι (Category.assoc _ _ _).symm c o o' ψ iso oV mVo
  have tjV := (hK p D R b N Y _ (s ≫ M.s) _ (s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).ι
    o o' oV oV' mVo mV' ψ ψV sqV).2 r w j tj
  obtain ⟨y₀, ⟨hy₀, m₀y, m₁y, hsq₀⟩, -⟩ := hY Y₀ s₀ o₀ o₀' ms₀ ψ₀ hp₀ iso₀ tj₀
  obtain ⟨v, ⟨hv, m₀v, m₁v, hsqv⟩, -⟩ :=
    hY₀ _ ((s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).ι ≫ s) oV oV' mV ψV hpV isoV tjV
  have hvy : v ≫ y₀ = (s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).ι := by
    apply (hY _ ((s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).ι ≫ s) oV oV' mV ψV hpV isoV tjV).unique
    · refine ⟨by rw [Category.assoc, hy₀, hv], ?_⟩
      obtain ⟨a, ha⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ m₀v m₀y
      obtain ⟨a', ha'⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ m₁v m₁y
      refine ⟨a, a', ?_⟩
      rw [ha, ha', Category.assoc m₀v.φ m₀y.φ, hsq₀, ← Category.assoc m₀v.φ, hsqv,
        Category.assoc (Over.Hom.left ψV) m₁v.φ m₁y.φ]
    · exact ⟨rfl, mVo, mV', sqV⟩
  let u : Y₀ ⟶ (s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).toScheme := hPB.lift gs y₀ (by rw [hgs, hy₀])
  have hu₁ : u ≫ s ∣_ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))) = gs := hPB.lift_fst _ _ _
  have hu₂ : u ≫ (s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).ι = y₀ := hPB.lift_snd _ _ _
  have hvg : v ≫ gs = s ∣_ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))) := by
    rw [← cancel_mono (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι, Category.assoc, hgs, hv, morphismRestrict_ι]
  have hvu : v ≫ u = 𝟙 _ := by
    apply hPB.hom_ext
    · rw [Category.assoc, hu₁, hvg, Category.id_comp]
    · rw [Category.assoc, hu₂, hvy, Category.id_comp]
  have huv : u ≫ v = 𝟙 Y₀ := by
    apply (hY₀ Y₀ s₀ o₀ o₀' ms₀ ψ₀ hp₀ iso₀ tj₀).unique
    · refine ⟨by rw [Category.assoc, hv, ← Category.assoc, hu₂, hy₀], ?_⟩
      have hc : (u ≫ v) ≫ y₀ = y₀ := by rw [Category.assoc, hvy, hu₂]
      obtain ⟨a, ha⟩ := (hT p D R b N hN hNp Y₀ Y₀ Y _ _ _ o₀ o₀ o (u ≫ v) y₀).2 y₀ hc m₀y m₀y
      obtain ⟨a', ha'⟩ := (hT p D R b N hN hNp Y₀ Y₀ Y _ _ _ o₀' o₀' o' (u ≫ v) y₀).2 y₀ hc m₁y m₁y
      refine ⟨a, a', ?_⟩
      apply m₁y.cart.1.hom_ext
      · rw [Category.assoc a.φ, ← hsq₀, ← Category.assoc a.φ, ha, hsq₀, Category.assoc (Over.Hom.left ψ₀) a'.φ, ha']
      · have e1 := a.cart.1.w
        have e2 := a'.cart.1.w
        calc (a.φ ≫ Over.Hom.left ψ₀) ≫ o₀'.A.hom = a.φ ≫ o₀.A.hom := by rw [Category.assoc a.φ, Over.w]
          _ = o₀.A.hom ≫ (u ≫ v) := e1
          _ = (Over.Hom.left ψ₀ ≫ o₀'.A.hom) ≫ (u ≫ v) := by rw [Over.w]
          _ = (Over.Hom.left ψ₀ ≫ a'.φ) ≫ o₀'.A.hom := by
            rw [Category.assoc (Over.Hom.left ψ₀) o₀'.A.hom, ← e2, Category.assoc (Over.Hom.left ψ₀) a'.φ]
    · refine ⟨Category.id_comp _, ?_⟩
      obtain ⟨i, hi⟩ := exists_id hT hN hNp ms₀
      obtain ⟨i', hi'⟩ := exists_id hT hN hNp m₁y
      exact ⟨i, i', by rw [hi, hi', Category.id_comp, Category.comp_id]⟩
  haveI : IsIso v := ⟨⟨u, hvu, huv⟩⟩
  rw [← hvg]
  infer_instance

theorem UpperTheory.Gal.crystallineComparison.Mod.tjExF_of :
    EsNorm → EsGen → ObjTri → PullIsog → PullKer → TjExF := by
  intro hE hG hT hI hK p _ D O _ _ _ _ f b N r w _ hS M j hj
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · have h1 := hS.norm
      rw [pow_zero, Ideal.absNorm_eq_one_iff] at h1
      exact absurd h1 (Ideal.IsMaximal.ne_top inferInstance)
    · exact h
  have hc : ∃ e : ℕ, p ^ (f * j) = p ^ e ∧ (0 < j → 0 < e) :=
    ⟨f * j, rfl, fun h => Nat.mul_pos hf h⟩
  obtain ⟨Y, s, t, o, o', ms, mt, ψ, st, fin, -, -, flat, iso, tj, univ⟩ :=
    hE p D O b N hS.three hS.cop hS.pmem r w j (p ^ (f * j)) inferInstance hS.ule hj hc hS.m1 M
  obtain ⟨Y₀, s₀, t₀, gs, gt, o₀, o₀', ms₀, mt₀, ψ₀, -, hgs, -, -, egs, -, -, iso₀, tj₀, univ₀⟩ :=
    hG p D O b N hS.three hS.cop hS.pmem r w j (p ^ (f * j)) inferInstance hS.ule hj hc hS.m1 M
  exact ⟨⟨Y, s, t, st, o, o', ms, mt, ψ, fin,
    et_of hT hI hK hS.three hS.cop ms iso tj univ gs hgs egs ms₀ iso₀ tj₀ univ₀, iso, tj, univ⟩, flat⟩
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private theorem reduced_of_finite_etale {K : Type} [Field K] {X : Scheme.{0}} (f : X ⟶ Sp K) [IsFinite f] [Etale f] : IsReduced X := by
  haveI : IsAffine X := isAffine_of_isAffineHom f
  have hE : (Scheme.Hom.appTop f).hom.Etale := HasRingHomProperty.appTop @Etale f inferInstance
  have hF : IsField Γ(Sp K, ⊤) :=
    MulEquiv.isField (Field.toIsField K)
      (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv
  letI : Field Γ(Sp K, ⊤) := hF.toField
  letI := (Scheme.Hom.appTop f).hom.toAlgebra
  haveI : Algebra.Etale Γ(Sp K, ⊤) Γ(X, ⊤) := hE.toAlgebra
  haveI : _root_.IsReduced Γ(X, ⊤) := Algebra.FormallyUnramified.isReduced_of_field Γ(Sp K, ⊤) Γ(X, ⊤)
  exact isReduced_of_isAffine_isReduced X

private theorem half_pt (hRead : PulledRead) (hKer : PullKer) {p : ℕ} [Fact p.Prime] {D : Datum p} {O : Type} [CommRing O]
    {b : Base D O} {N : ℕ} {M : Model b N} {r : ℤ} {w : Ideal (𝓞 D.F)} {j c : ℕ} (T : TjD M r w j c)
    {K : Type} [Field K] [IsAlgClosed K] [CharZero K] (x : Sp K ⟶ M.X) (y y' : Sp K ⟶ T.Y)
    (hy : y ≫ T.s = x) (hy' : y' ≫ T.s = x)
    (hag : ∀ g : Over.mk x ⟶ M.univ.A, KilledBy M.univ w g → KerAt T y g.left → KerAt T y' g.left)
    {o₁ : Obj b N (x ≫ M.s)} (m₁ : ObjMap o₁ M.univ x) (P : Pulled T m₁ y) (P' : Pulled T m₁ y')
    (a : 𝟙_ (Over (Sp K)) ⟶ o₁.A) (ha : UKer r o₁ P.ψ _ a) : a ≫ P'.ψ = 1 := by
  have hR := (hRead p D O b N M r w j c T (Sp K) x (x ≫ M.s) o₁ m₁ y hy P a).1
  have hR' := (hRead p D O b N M r w j c T (Sp K) x (x ≫ M.s) o₁ m₁ y' hy' P' a).1
  have hkw : KilledBy o₁ w a := (P.tj K (𝟙 _)).1 a ha.1 ha.2
  have hw : (Over.Hom.left a ≫ m₁.φ) ≫ M.univ.A.hom = x := by
    rw [Category.assoc, m₁.cart.1.w, ← Category.assoc, Over.w a]
    exact Category.id_comp x
  obtain ⟨g, hg⟩ : ∃ g : Over.mk x ⟶ M.univ.A, Over.Hom.left g = Over.Hom.left a ≫ m₁.φ :=
    ⟨@Over.homMk _ _ _ (Over.mk x) M.univ.A (Over.Hom.left a ≫ m₁.φ : Sp K ⟶ M.univ.A.left) hw, rfl⟩
  have hK := (hKer p D O b N M.X (Sp K) M.s (x ≫ M.s) x M.univ M.univ o₁ o₁ m₁ m₁ (𝟙 _) (𝟙 _)
    (by simp)).1 (𝟙_ (Over (Sp K))) (Over.mk x) rfl a g (by rw [hg, eqToHom_refl, Category.id_comp])
  have hkg : KilledBy M.univ w g := (hK.2.2 w).1 hkw
  have h1 := hag g hkg (by rw [hg]; exact hR.1 ha.1)
  rw [hg] at h1
  exact hR'.2 h1

private theorem half_ker (hRead : PulledRead) (hKer : PullKer) {p : ℕ} [Fact p.Prime] {D : Datum p} {O : Type} [CommRing O]
    {b : Base D O} {N : ℕ} (hN : 3 ≤ N) (hNp : N.Coprime p) (hm : D.m = 1) {M : Model b N} {r : ℤ} {w : Ideal (𝓞 D.F)}
    (hw : w.IsMaximal) (hu : uIdeal D r ≤ w) {j c : ℕ} (hj : j ≤ D.n) (hc : ∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) (T : TjD M r w j c)
    {K : Type} [Field K] [IsAlgClosed K] [CharZero K] (hpU : IsUnit ((p : ℕ) : Γ(Sp K, ⊤))) (x : Sp K ⟶ M.X) (y y' : Sp K ⟶ T.Y)
    (hy : y ≫ T.s = x) (hy' : y' ≫ T.s = x)
    (hag : ∀ g : Over.mk x ⟶ M.univ.A, KilledBy M.univ w g → KerAt T y g.left → KerAt T y' g.left)
    {o₁ : Obj b N (x ≫ M.s)} (m₁ : ObjMap o₁ M.univ x) (P : Pulled T m₁ y) (P' : Pulled T m₁ y')
    (U : Over (Sp K)) (g : U ⟶ o₁.A) (hg : UKer r o₁ P.ψ U g) : UKer r o₁ P'.ψ U g := by
  obtain ⟨Ks, e, i, -, -, hfin, het, -, -, hiff⟩ := GlobalTheory.UPel.HT.ES.KerUPart.exists_kerUPart p D O b N hN hNp hm r w j c
    hw hu hj hc (Sp K) (x ≫ M.s) hpU o₁ P.o' P.ψ P.isog P.tj
  refine ⟨?_, hg.2⟩
  obtain ⟨z, rfl⟩ := (hiff U g).1 hg
  suffices hi : i ≫ P'.ψ = 1 by
    rw [Category.assoc, hi]
    simp
  haveI : IsFinite Ks.hom := hfin
  haveI : Etale Ks.hom := het
  haveI : IsReduced Ks.left := reduced_of_finite_etale Ks.hom
  haveI : IsProper P'.o'.A.hom := IsAbelianScheme.proper (self := P'.o'.ab)
  haveI : Smooth P'.o'.A.hom := IsAbelianScheme.smooth (self := P'.o'.ab)
  have hw1 : Over.Hom.left (i ≫ P'.ψ) ≫ P'.o'.A.hom = Ks.hom := Over.w _
  haveI : LocallyOfFiniteType (Over.Hom.left (i ≫ P'.ψ) ≫ P'.o'.A.hom) := by
    rw [hw1]
    infer_instance
  apply Over.OverMorphism.ext
  refine ext_of_apply_eq P'.o'.A.hom Set.univ isClosed_univ.isLocallyClosed dense_univ ?_ ?_
  · intro pt _ hpt
    obtain ⟨aK, haK⟩ : ∃ aK : 𝟙_ (Over (Sp K)) ⟶ Ks, Over.Hom.left aK = pointOfClosedPoint Ks.hom pt hpt :=
      ⟨Over.homMk (pointOfClosedPoint Ks.hom pt hpt) (pointOfClosedPoint_comp Ks.hom pt hpt), rfl⟩
    have h0 : (aK ≫ i) ≫ P'.ψ = 1 :=
      half_pt hRead hKer T x y y' hy hy' hag m₁ P P' (aK ≫ i) ((hiff _ _).2 ⟨aK, rfl⟩)
    have hp1 : pt = (pointOfClosedPoint Ks.hom pt hpt) (IsLocalRing.closedPoint K) :=
      (pointOfClosedPoint_apply Ks.hom pt hpt _).symm
    have e1 : (pointOfClosedPoint Ks.hom pt hpt ≫ Over.Hom.left (i ≫ P'.ψ)) (IsLocalRing.closedPoint K) =
        (pointOfClosedPoint Ks.hom pt hpt ≫ Over.Hom.left (1 : Ks ⟶ P'.o'.A)) (IsLocalRing.closedPoint K) := by
      rw [← haK, ← Over.comp_left, ← Over.comp_left, ← Category.assoc, h0]
      simp
    rw [hp1]
    exact e1
  · rw [Over.w, Over.w]

private theorem charZero_of_pt {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] {p : ℕ}
    (hp : (p : O) ∈ IsLocalRing.maximalIdeal O) {K : Type} [Field K] (hK : (p : K) ≠ 0) (s : Sp K ⟶ Sp O) : CharZero K := by
  let φ : O →+* K := (Spec.preimage s).hom
  have hφp : φ p = (p : K) := map_natCast φ p
  haveI : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  by_cases hb : RingHom.ker φ = ⊥
  · exact charZero_of_injective_ringHom ((RingHom.injective_iff_ker_eq_bot φ).2 hb)
  · exfalso
    have hmax : (RingHom.ker φ).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hb
    have hm : RingHom.ker φ = IsLocalRing.maximalIdeal O := IsLocalRing.eq_maximalIdeal hmax
    apply hK
    rw [← hφp, ← RingHom.mem_ker, hm]
    exact hp

theorem UpperTheory.Gal.crystallineComparison.Mod.secInj_of :
    PulledEx → PulledRead → PullKer → KerFromU → IsoOfKer → SecInj := by
  intro hEx hRead hKer hKF hIso p _ D O _ _ _ _ f b N r w _ hStd M j hj T K _ _ hp x y y' hy hy' hag
  haveI : CharZero K := charZero_of_pt hStd.pmem hp (x ≫ M.s)
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · have hcard := hStd.card
      rw [h, pow_zero, Nat.card_eq_one_iff_unique] at hcard
      exact (not_subsingleton_iff_nontrivial.2 inferInstance hcard.1).elim
    · exact h
  have hpU : IsUnit ((p : ℕ) : Γ(Sp K, ⊤)) := by
    have := (IsUnit.mk0 _ hp).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
    simpa using this
  have hc : ∃ e : ℕ, p ^ (f * j) = p ^ e ∧ (0 < j → 0 < e) := ⟨f * j, rfl, fun h => Nat.mul_pos hf h⟩
  obtain ⟨o₁, ⟨m₁⟩⟩ := GlobalTheory.T.exists_harrisTaylorObject_pullback p D O b N M.X (Sp K) M.s x M.univ
  obtain ⟨P⟩ := hEx p D O b N hStd.three hStd.cop M r w j _ T (Sp K) x (x ≫ M.s) rfl o₁ m₁ y hy
  obtain ⟨P'⟩ := hEx p D O b N hStd.three hStd.cop M r w j _ T (Sp K) x (x ≫ M.s) rfl o₁ m₁ y' hy'
  have hU : ∀ U g, UKer r o₁ P.ψ U g ↔ UKer r o₁ P'.ψ U g := fun U g =>
    ⟨half_ker hRead hKer hStd.three hStd.cop hStd.m1 inferInstance hStd.ule hj hc T hpU x y y' hy hy'
        (fun g h => (hag g h).1) m₁ P P' U g,
      half_ker hRead hKer hStd.three hStd.cop hStd.m1 inferInstance hStd.ule hj hc T hpU x y' y hy' hy
        (fun g h => (hag g h).2) m₁ P' P U g⟩
  have hne : w ≠ ⊤ := Ideal.IsMaximal.ne_top inferInstance
  have hker : ∀ (U : Over (Sp K)) (g : U ⟶ o₁.A), g ≫ P.ψ = 1 ↔ g ≫ P'.ψ = 1 := fun U g =>
    ⟨hKF p D O b N r w hne hStd.ule K (x ≫ M.s) _ o₁ P.o' P'.o' P.ψ P'.ψ P.isog P'.isog hU U g,
      hKF p D O b N r w hne hStd.ule K (x ≫ M.s) _ o₁ P'.o' P.o' P'.ψ P.ψ P'.isog P.isog (fun U g => (hU U g).symm) U g⟩
  obtain ⟨m, hmφ⟩ := hIso p D O b N K (x ≫ M.s) _ o₁ P.o' P'.o' P.ψ P'.ψ P.isog P'.isog hker
  obtain ⟨n, hn⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ m P'.m'
  have hex : ∃ n' : ObjMap P.o' T.o' y', n'.φ = m.φ ≫ P'.m'.φ := by
    revert n hn
    rw [Category.id_comp]
    exact fun n hn => ⟨n, hn⟩
  obtain ⟨n', hn'⟩ := hex
  exact (T.univ (Sp K) x o₁ P.o' m₁ P.ψ hpU P.isog P.tj).unique ⟨hy, P.m₀, P.m', P.sq⟩
    ⟨hy', P'.m₀, n', by rw [P'.sq, hn', ← hmφ, Category.assoc]⟩
end
