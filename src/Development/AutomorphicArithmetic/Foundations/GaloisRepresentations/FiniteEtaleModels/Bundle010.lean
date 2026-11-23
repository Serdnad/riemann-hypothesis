module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.Bundle003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PairCalc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle510
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharZeroOfIsUnit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1159
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
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
import Mathlib.Tactic.Basify
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
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.IsEtIdealOfPlace

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.crystallineComparison.Mod (Std TjD KerAt)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.tjExG_of :
    UpperTheory.Gal.crystallineComparison.Mod.EsNorm → UpperTheory.Gal.crystallineComparison.Mod.EsGen → UpperTheory.Gal.crystallineComparison.Mod.ObjTri → UpperTheory.Gal.crystallineComparison.Mod.PullIsog → UpperTheory.Gal.crystallineComparison.Mod.PullKer → TjExG := by
  intro hN hG hT hPI hPK p _ D R _ _ _ _ b N h3 hcp hpm hm1 r w j e hw hle hj he M
  obtain ⟨Y, s, t, o, o', ms, mt, ψ, hst, hfs, -, -, -, hiso, htj, hu⟩ :=
    hN p D R b N h3 hcp hpm r w j (p ^ e) hw hle hj ⟨e, rfl, he⟩ hm1 M
  obtain ⟨Y₀, s₀, t₀, gs, gt, o₀, o₀', ms₀, mt₀, ψ₀, -, hgs, -, -, hgse, -, -, hiso0, htj0, hu0⟩ :=
    hG p D R b N h3 hcp hpm r w j (p ^ e) hw hle hj ⟨e, rfl, he⟩ hm1 M
  let U := M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))
  let V := s ⁻¹ᵁ U
  have het : Etale (s ∣_ U) := by
    have hpU : IsUnit ((p : ℕ) : Γ(U.toScheme, ⊤)) := by
      have h := GlobalTheory.EtC.PairDich.isUnit_ι_appTop U ((p : ℕ) : Γ(M.X, ⊤)) le_rfl
      rwa [map_natCast] at h
    have hp₀ : IsUnit ((p : ℕ) : Γ(Y₀, ⊤)) := by
      simpa only [map_natCast] using hpU.map gs.appTop.hom
    have hpV : IsUnit ((p : ℕ) : Γ(V.toScheme, ⊤)) := by
      simpa only [map_natCast] using hpU.map (s ∣_ U).appTop.hom
    have hPB := isPullback_morphismRestrict s U
    obtain ⟨oV, ⟨mV⟩⟩ := GlobalTheory.T.exists_harrisTaylorObject_pullback p D R b N
      M.X V.toScheme M.s (V.ι ≫ s) M.univ
    obtain ⟨mVo, -⟩ := (hT p D R b N h3 hcp _ Y M.X _ (s ≫ M.s) M.s oV o M.univ V.ι s).2
      _ rfl mV ms
    obtain ⟨oV', mV', ψV, isoV, sqV⟩ := hPI p D R b N Y V.toScheme (s ≫ M.s) _ V.ι
      (Category.assoc _ _ _).symm (p ^ e) o o' ψ hiso oV mVo
    have tjV := (hPK p D R b N Y _ (s ≫ M.s) _ V.ι o o' oV oV' mVo mV' ψ ψV sqV).2 r w j htj
    obtain ⟨y₀, ⟨hy₀, m₀y, m₁y, hsq₀⟩, -⟩ := hu Y₀ s₀ o₀ o₀' ms₀ ψ₀ hp₀ hiso0 htj0
    obtain ⟨v, ⟨hv, m₀v, m₁v, hsqv⟩, -⟩ := hu0 _ (V.ι ≫ s) oV oV' mV ψV hpV isoV tjV
    have hvy : v ≫ y₀ = V.ι := by
      apply (hu _ (V.ι ≫ s) oV oV' mV ψV hpV isoV tjV).unique
      · refine ⟨by rw [Category.assoc, hy₀, hv], ?_⟩
        obtain ⟨a, ha⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ m₀v m₀y
        obtain ⟨a', ha'⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ m₁v m₁y
        refine ⟨a, a', ?_⟩
        rw [ha, ha', Category.assoc m₀v.φ m₀y.φ, hsq₀, ← Category.assoc m₀v.φ, hsqv,
          Category.assoc (Over.Hom.left ψV) m₁v.φ m₁y.φ]
      · exact ⟨rfl, mVo, mV', sqV⟩
    let u : Y₀ ⟶ V.toScheme := hPB.lift gs y₀ (by rw [hgs, hy₀])
    have hu₁ : u ≫ s ∣_ U = gs := hPB.lift_fst _ _ _
    have hu₂ : u ≫ V.ι = y₀ := hPB.lift_snd _ _ _
    have hvg : v ≫ gs = s ∣_ U := by
      rw [← cancel_mono U.ι, Category.assoc, hgs, hv, morphismRestrict_ι]
    have hvu : v ≫ u = 𝟙 _ := by
      apply hPB.hom_ext
      · rw [Category.assoc, hu₁, hvg, Category.id_comp]
      · rw [Category.assoc, hu₂, hvy, Category.id_comp]
    have huv : u ≫ v = 𝟙 Y₀ := by
      apply (hu0 Y₀ s₀ o₀ o₀' ms₀ ψ₀ hp₀ hiso0 htj0).unique
      · refine ⟨by rw [Category.assoc, hv, ← Category.assoc, hu₂, hy₀], ?_⟩
        have hc : (u ≫ v) ≫ y₀ = y₀ := by rw [Category.assoc, hvy, hu₂]
        obtain ⟨a, ha⟩ := (hT p D R b N h3 hcp Y₀ Y₀ Y _ _ _ o₀ o₀ o (u ≫ v) y₀).2 y₀ hc m₀y m₀y
        obtain ⟨a', ha'⟩ := (hT p D R b N h3 hcp Y₀ Y₀ Y _ _ _ o₀' o₀' o' (u ≫ v) y₀).2
          y₀ hc m₁y m₁y
        refine ⟨a, a', ?_⟩
        apply m₁y.cart.1.hom_ext
        · rw [Category.assoc a.φ, ← hsq₀, ← Category.assoc a.φ, ha, hsq₀,
            Category.assoc (Over.Hom.left ψ₀) a'.φ, ha']
        · have e1 := a.cart.1.w
          have e2 := a'.cart.1.w
          calc (a.φ ≫ Over.Hom.left ψ₀) ≫ o₀'.A.hom = a.φ ≫ o₀.A.hom := by rw [Category.assoc a.φ, Over.w]
            _ = o₀.A.hom ≫ (u ≫ v) := e1
            _ = (Over.Hom.left ψ₀ ≫ o₀'.A.hom) ≫ (u ≫ v) := by rw [Over.w]
            _ = (Over.Hom.left ψ₀ ≫ a'.φ) ≫ o₀'.A.hom := by
              rw [Category.assoc (Over.Hom.left ψ₀) o₀'.A.hom, ← e2,
                Category.assoc (Over.Hom.left ψ₀) a'.φ]
      · refine ⟨Category.id_comp _, ?_⟩
        have existsId {S S₃ : Scheme.{0}} {s : S ⟶ Sp R} {s₃ : S₃ ⟶ Sp R}
            {o : Obj b N s} {o₃ : Obj b N s₃} {g : S ⟶ S₃} (m : ObjMap o o₃ g) :
            ∃ i : ObjMap o o (𝟙 S), i.φ = 𝟙 _ := by
          obtain ⟨i, hi⟩ := (hT p D R b N h3 hcp _ _ _ _ _ _ o o o₃ (𝟙 S) g).2 g
            (Category.id_comp g) m m
          refine ⟨i, m.cart.1.hom_ext ?_ ?_⟩
          · rw [hi, Category.id_comp]
          · rw [i.cart.1.w, Category.comp_id, Category.id_comp]
        obtain ⟨i, hi⟩ := existsId ms₀
        obtain ⟨i', hi'⟩ := existsId m₁y
        exact ⟨i, i', by rw [hi, hi', Category.id_comp, Category.comp_id]⟩
    have : IsIso v := ⟨⟨u, hvu, huv⟩⟩
    rw [← hvg]
    infer_instance
  exact ⟨⟨Y, s, t, hst, o, o', ms, mt, ψ, hfs, het, hiso, htj, hu⟩⟩
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.crystallineComparison.Mod (Std TjD KerAt Pulled UKer)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.secInjG_of :
    UpperTheory.Gal.crystallineComparison.Mod.PulledEx → UpperTheory.Gal.crystallineComparison.Mod.PulledRead → UpperTheory.Gal.crystallineComparison.Mod.PullKer → UpperTheory.Gal.crystallineComparison.Mod.KerFromU → UpperTheory.Gal.crystallineComparison.Mod.IsoOfKer → SecInjG := by
  intro hPE hPR hPK hKU hIK p _ D R _ b N hN hNp hm r w j e hw hu hj he M T K _ _ _ x y y' hy hy' hK
  have hpK0 : IsUnit ((p : ℕ) : K) := by
    refine IsUnit.mk0 _ ?_
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpK : IsUnit ((p : ℕ) : Γ(Sp K, ⊤)) := by
    have := hpK0.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
    simpa using this
  obtain ⟨o₁, ⟨m₁⟩⟩ := GlobalTheory.T.exists_harrisTaylorObject_pullback p D R b N M.X (Sp K) M.s x M.univ
  obtain ⟨P⟩ := hPE p D R b N hN hNp M r w j (p ^ e) T (Sp K) x (x ≫ M.s) rfl o₁ m₁ y hy
  obtain ⟨P'⟩ := hPE p D R b N hN hNp M r w j (p ^ e) T (Sp K) x (x ≫ M.s) rfl o₁ m₁ y' hy'
  have hc : ∃ e', p ^ e = p ^ e' ∧ (0 < j → 0 < e') := ⟨e, rfl, he⟩
  have kernel_imp (z z' : Sp K ⟶ T.Y) (hz : z ≫ T.s = x) (hz' : z' ≫ T.s = x)
      (hpoint : ∀ a : Over.mk x ⟶ M.univ.A,
        ES.KilledBy M.univ w a → KerAt T z a.left → KerAt T z' a.left)
      (Q : Pulled T m₁ z) (Q' : Pulled T m₁ z') (U : Over (Sp K)) (g : U ⟶ o₁.A)
      (hg : UKer r o₁ Q.ψ U g) : UKer r o₁ Q'.ψ U g := by
    obtain ⟨S, -, i, -, -, hfin, het, -, -, hiff⟩ :=
      ES.KerUPart.exists_kerUPart p D R b N hN hNp hm r w j (p ^ e)
        hw hu hj hc (Sp K) (x ≫ M.s) hpK o₁ Q.o' Q.ψ Q.isog Q.tj
    refine ⟨?_, hg.2⟩
    obtain ⟨v, rfl⟩ := (hiff U g).1 hg
    suffices hi : i ≫ Q'.ψ = 1 by
      rw [Category.assoc, hi]
      simp
    have : IsReduced S.left := by
      have : IsAffine S.left := isAffine_of_isAffineHom S.hom
      have hE : (Scheme.Hom.appTop S.hom).hom.Etale :=
        HasRingHomProperty.appTop @Etale S.hom het
      have hF : IsField Γ(Sp K, ⊤) :=
        MulEquiv.isField (Field.toIsField K)
          (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv
      let : Field Γ(Sp K, ⊤) := hF.toField
      let := (Scheme.Hom.appTop S.hom).hom.toAlgebra
      have : Algebra.Etale Γ(Sp K, ⊤) Γ(S.left, ⊤) := hE.toAlgebra
      have : _root_.IsReduced Γ(S.left, ⊤) :=
        Algebra.FormallyUnramified.isReduced_of_field Γ(Sp K, ⊤) Γ(S.left, ⊤)
      exact isReduced_of_isAffine_isReduced S.left
    have : IsProper Q'.o'.A.hom := IsAbelianScheme.proper (self := Q'.o'.ab)
    have : Smooth Q'.o'.A.hom := IsAbelianScheme.smooth (self := Q'.o'.ab)
    have : LocallyOfFiniteType ((i ≫ Q'.ψ).left ≫ Q'.o'.A.hom) := by
      rw [Over.w]
      infer_instance
    apply Over.OverMorphism.ext
    refine ext_of_apply_eq Q'.o'.A.hom Set.univ isClosed_univ.isLocallyClosed dense_univ ?_ ?_
    · intro pt _ hpt
      let aK : 𝟙_ (Over (Sp K)) ⟶ S :=
        Over.homMk (pointOfClosedPoint S.hom pt hpt) (pointOfClosedPoint_comp S.hom pt hpt)
      let a := aK ≫ i
      have ha : UKer r o₁ Q.ψ _ a := (hiff _ _).2 ⟨aK, rfl⟩
      have hR := (hPR p D R b N M r w j (p ^ e) T (Sp K) x (x ≫ M.s) o₁ m₁ z hz Q a).1
      have hR' := (hPR p D R b N M r w j (p ^ e) T (Sp K) x (x ≫ M.s) o₁ m₁ z' hz' Q' a).1
      have hkw : ES.KilledBy o₁ w a := (Q.tj K (𝟙 _)).1 a ha.1 ha.2
      have hbase : (a.left ≫ m₁.φ) ≫ M.univ.A.hom = x := by
        rw [Category.assoc, m₁.cart.1.w, ← Category.assoc, Over.w a]
        exact Category.id_comp x
      let a₀ : Over.mk x ⟶ M.univ.A := Over.homMk (a.left ≫ m₁.φ) hbase
      have htransport := (hPK p D R b N M.X (Sp K) M.s (x ≫ M.s) x M.univ M.univ o₁ o₁ m₁ m₁
        (𝟙 _) (𝟙 _) (by simp)).1 (𝟙_ (Over (Sp K))) (Over.mk x) rfl a a₀ (by
          rw [eqToHom_refl, Category.id_comp]
          rfl)
      have hzero : a ≫ Q'.ψ = 1 := hR'.2 (hpoint a₀ ((htransport.2.2 w).1 hkw) (hR.1 ha.1))
      have hclosed : aK.left (IsLocalRing.closedPoint K) = pt := pointOfClosedPoint_apply S.hom pt hpt _
      have heq : aK ≫ (i ≫ Q'.ψ) = aK ≫ (1 : S ⟶ Q'.o'.A) := by
        rw [← Category.assoc, show aK ≫ i = a from rfl, hzero]
        simp
      rw [← hclosed]
      exact congrArg (fun f : 𝟙_ (Over (Sp K)) ⟶ Q'.o'.A => f.left (IsLocalRing.closedPoint K)) heq
    · rw [Over.w, Over.w]
  have k1 := kernel_imp y y' hy hy' (fun g hg => (hK g hg).1) P P'
  have k2 := kernel_imp y' y hy' hy (fun g hg => (hK g hg).2) P' P
  have hker : ∀ (U : Over (Sp K)) (g : U ⟶ o₁.A), g ≫ P.ψ = 1 ↔ g ≫ P'.ψ = 1 := by
    intro U g
    constructor
    · exact hKU p D R b N r w hw.ne_top hu K (x ≫ M.s) (p ^ e) o₁ P.o' P'.o' P.ψ P'.ψ P.isog P'.isog
        (fun U g => ⟨k1 U g, k2 U g⟩) U g
    · exact hKU p D R b N r w hw.ne_top hu K (x ≫ M.s) (p ^ e) o₁ P'.o' P.o' P'.ψ P.ψ P'.isog P.isog
        (fun U g => ⟨k2 U g, k1 U g⟩) U g
  obtain ⟨m, hm'⟩ := hIK p D R b N K (x ≫ M.s) (p ^ e) o₁ P.o' P'.o' P.ψ P'.ψ P.isog P'.isog hker
  obtain ⟨m'', hm''⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ m P'.m'
  have hU := T.univ (Sp K) x o₁ P.o' m₁ P.ψ hpK P.isog P.tj
  have fix : ∀ (f : Sp K ⟶ T.Y) (_ : f = y') (n : GlobalTheory.UPel.HT.ObjMap P.o' T.o' f),
      ∃ n' : GlobalTheory.UPel.HT.ObjMap P.o' T.o' y', n'.φ = n.φ := by
    rintro f rfl n
    exact ⟨n, rfl⟩
  obtain ⟨n', hn'⟩ := fix _ (Category.id_comp y') m''
  refine hU.unique ⟨hy, P.m₀, P.m', P.sq⟩ ⟨hy', P'.m₀, n', ?_⟩
  rw [hn', hm'', ← Category.assoc, hm', P'.sq]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.crystallineComparison.Mod (Std TjD KerAt)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

private theorem isUnit_nat_of {E : Type} [Field E] [CharZero E] {V : Scheme.{0}} (s : V ⟶ Sp E) (n : ℕ) (hn : n ≠ 0) :
    IsUnit ((n : ℕ) : Γ(V, ⊤)) := by
  have hE : IsUnit ((n : E)) := (Nat.cast_ne_zero.mpr hn).isUnit
  have h1 : IsUnit ((n : Γ(Sp E, ⊤))) := by
    have := hE.map (Scheme.ΓSpecIso (CommRingCat.of E)).inv.hom
    simpa using this
  have := h1.map s.appTop.hom
  simpa using this

section
variable {q : ℕ} [Fact q.Prime] {D : Datum q} {R R' : Type} [CommRing R] [CommRing R'] [Algebra ℚ R'] {b : Base D R}
  {gb : GBase D.toG R'}

private theorem qmap_cast {N₁ N c : ℕ} {V Y : Scheme.{0}} {s : V ⟶ Sp R'} {t : Y ⟶ Sp R} {a : GObj gb N₁ s} {u : Obj b N t}
    {f f' : V ⟶ Y} (h : f = f') (n : QMap a u f c) : ∃ n' : QMap a u f' c, n'.φ = n.φ := by
  subst h
  exact ⟨n, rfl⟩

private theorem rigid_of (hO : UpperTheory.Gal.crystallineComparison.Mod.ObjTri) {N : ℕ} (hN : 3 ≤ N) (hNq : N.Coprime q) {S₁ S₂ : Scheme.{0}}
    {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {o₁ : Obj b N s₁} {o₂ : Obj b N s₂} {f f' : S₁ ⟶ S₂}
    (m : ObjMap o₁ o₂ f) (m' : ObjMap o₁ o₂ f') (h : f = f') : m.φ = m'.φ := by
  subst h
  exact (hO q D R b N hN hNq S₁ S₂ S₂ s₁ s₂ s₂ o₁ o₂ o₂ f (𝟙 _)).1 m m'

private theorem read_tj {N : ℕ} {M : Model b N} {r : ℤ} {w : Ideal (𝓞 D.F)} {j c : ℕ} (Tj : TjD M r w j c) {V : Scheme.{0}}
    (x : V ⟶ M.X) (s₀ : V ⟶ Sp R) (hx : x ≫ M.s = s₀) (o₁ o₂ : Obj b N s₀) (m : ObjMap o₁ M.univ x) (ψ₀ : o₁.A ⟶ o₂.A)
    (hu : IsUnit ((q : ℕ) : Γ(V, ⊤))) (hi : ES.IsPIsog c o₁ o₂ ψ₀) (ht : ES.IsTj r w j o₁ o₂ ψ₀) :
    ∃ (y : V ⟶ Tj.Y) (_ : y ≫ Tj.s = x) (m₀ : ObjMap o₁ Tj.o y) (m₁ : ObjMap o₂ Tj.o' y),
      m₀.φ ≫ Tj.ψ.left = ψ₀.left ≫ m₁.φ := by
  subst hx
  obtain ⟨y, ⟨hy, m₀, m₁, h⟩, -⟩ := Tj.univ V x o₁ o₂ m ψ₀ hu hi ht
  exact ⟨y, hy, m₀, m₁, h⟩

private theorem read_core (hQ : QComp) (hO : UpperTheory.Gal.crystallineComparison.Mod.ObjTri) {N N₁ N₂ c₁ c₂ : ℕ} (hN : 3 ≤ N) (hNq : N.Coprime q)
    {M : Model b N} {r : ℤ} {w : Ideal (𝓞 D.F)} {j c : ℕ} (Tj : TjD M r w j c)
    {V Y₁ Y₂ : Scheme.{0}} {s : V ⟶ Sp R'} {s₀ : V ⟶ Sp R} {t₁ : Y₁ ⟶ Sp R} {t₂ : Y₂ ⟶ Sp R}
    {a : GObj gb N₁ s} {a' : GObj gb N₂ s} {o₁ o₂ : Obj b N s₀} {u₁ : Obj b N t₁} {u₂ : Obj b N t₂}
    (n₁ : QMap a o₁ (𝟙 V) c₁) (n₂ : QMap a' o₂ (𝟙 V) c₂) {j₁ : V ⟶ Y₁} {j₂ : V ⟶ Y₂}
    (k₁ : QMap a u₁ j₁ c₁) (k₂ : QMap a' u₂ j₂ c₂) {f : Y₁ ⟶ M.X} {π : Y₂ ⟶ M.X}
    (mf : ObjMap u₁ M.univ f) (mπ : ObjMap u₂ M.univ π)
    (hb₁ : (j₁ ≫ f) ≫ M.s = s₀) (hb₂ : (j₂ ≫ π) ≫ M.s = s₀)
    (ψ' : a.A.left ⟶ a'.A.left) (ψ₀ : o₁.A ⟶ o₂.A) (hψ : n₁.φ ≫ ψ₀.left = ψ' ≫ n₂.φ)
    (hu : IsUnit ((q : ℕ) : Γ(V, ⊤))) (hi : ES.IsPIsog c o₁ o₂ ψ₀) (ht : ES.IsTj r w j o₁ o₂ ψ₀) :
    ∃ (y : V ⟶ Tj.Y) (fa : a.A.left ⟶ Tj.o.A.left) (fb : a'.A.left ⟶ Tj.o'.A.left),
      y ≫ Tj.s = j₁ ≫ f ∧ y ≫ Tj.t = j₂ ≫ π ∧ IsGrpPullback a.A Tj.o.A y fa ∧ IsGrpPullback a'.A Tj.o'.A y fb ∧
      fa ≫ Tj.ψ.left = ψ' ≫ fb ∧ fa ≫ Tj.ms.φ = k₁.φ ≫ mf.φ ∧ fb ≫ Tj.mt.φ = k₂.φ ≫ mπ.φ := by
  obtain ⟨k₁', hk₁'⟩ := qmap_cast (Category.id_comp j₁).symm k₁
  obtain ⟨k₂', hk₂'⟩ := qmap_cast (Category.id_comp j₂).symm k₂
  obtain ⟨m₁, hm₁⟩ := (hQ q D R R' b gb N₁ N c₁ V V Y₁ s s₀ t₁ a o₁ u₁ (𝟙 V) j₁).2.2.1 inferInstance n₁ k₁'
  obtain ⟨m₂, hm₂⟩ := (hQ q D R R' b gb N₂ N c₂ V V Y₂ s s₀ t₂ a' o₂ u₂ (𝟙 V) j₂).2.2.1 inferInstance n₂ k₂'
  obtain ⟨mx, hmx⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ m₁ mf
  obtain ⟨mz, hmz⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ m₂ mπ
  obtain ⟨y, hy, m₀, m', hsq⟩ := read_tj Tj (j₁ ≫ f) s₀ hb₁ o₁ o₂ mx ψ₀ hu hi ht
  obtain ⟨e₁, he₁⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ m' Tj.mt
  obtain ⟨e₀, he₀⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ m₀ Tj.ms
  have hbt : (y ≫ Tj.t) ≫ M.s = s₀ := by
    rw [Category.assoc, ← Tj.st, ← Category.assoc, hy, hb₁]
  have yt : y ≫ Tj.t = j₂ ≫ π := (M.rep V s₀ o₂).unique ⟨hbt, ⟨e₁⟩⟩ ⟨hb₂, ⟨mz⟩⟩
  obtain ⟨p₁, hp₁⟩ := (hQ q D R R' b gb N₁ N c₁ V V Tj.Y s s₀ (Tj.s ≫ M.s) a o₁ Tj.o (𝟙 V) y).1 n₁ m₀
  obtain ⟨p₂, hp₂⟩ := (hQ q D R R' b gb N₂ N c₂ V V Tj.Y s s₀ (Tj.s ≫ M.s) a' o₂ Tj.o' (𝟙 V) y).1 n₂ m'
  have r₀ : m₀.φ ≫ Tj.ms.φ = m₁.φ ≫ mf.φ := by
    rw [← he₀, ← hmx]
    exact rigid_of hO hN hNq e₀ mx hy
  have r₁ : m'.φ ≫ Tj.mt.φ = m₂.φ ≫ mπ.φ := by
    rw [← he₁, ← hmz]
    exact rigid_of hO hN hNq e₁ mz yt
  refine ⟨y, n₁.φ ≫ m₀.φ, n₂.φ ≫ m'.φ, hy, yt, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨p₁', hp₁'⟩ := qmap_cast (Category.id_comp y) p₁
    have := p₁'.cart
    rw [hp₁', hp₁] at this
    exact this
  · obtain ⟨p₂', hp₂'⟩ := qmap_cast (Category.id_comp y) p₂
    have := p₂'.cart
    rw [hp₂', hp₂] at this
    exact this
  · rw [Category.assoc, hsq, ← Category.assoc, hψ, Category.assoc]
  · rw [Category.assoc, r₀, ← Category.assoc, ← hm₁, hk₁']
  · rw [Category.assoc, r₁, ← Category.assoc, ← hm₂, hk₂']

end

theorem UpperTheory.Gal.FiniteEtaleModels.bRead_of :
    IsogG → QObj → QComp → UpperTheory.Gal.crystallineComparison.Mod.ObjTri → BRead := by
  intro hI hQO hQC hO p _ D G L _ E _ _ gb w q _ r 𝔴 𝔫 S k T N₀ 𝔟₁ 𝔟₂ X₁ X₂ 𝔴' i hmax hu hle hin h hint htj M₁ M₂ c₁ c₂ a₁ a₂ hn₁ hn₂
    C₁ C₂ W f mf hf e he he0 Tj
  have h3 : 3 ≤ N₀ := X₁.lev.1
  have hcq : N₀.Coprime q := X₁.lev.2.1
  have hM₁ : M₁.1 = N₀ * c₁ := hn₁.1
  have hM₂ : M₂.1 = N₀ * c₂ := hn₂.1
  have pos₁ : 0 < M₁.1 := by have := M₁.2.1; omega
  have pos₂ : 0 < M₂.1 := by have := M₂.2.1; omega
  obtain ⟨o₁, ⟨n₁⟩⟩ := hQO q (datAt S.atq S.sp) (Ow w) E S.b gb (algebraMap (Ow w) E) S.mat M₁.1 N₀ c₁ hM₁ pos₁ hcq _ _ (T.M M₁).univ
  obtain ⟨o₂, ⟨n₂⟩⟩ := hQO q (datAt S.atq S.sp) (Ow w) E S.b gb (algebraMap (Ow w) E) S.mat M₂.1 N₀ c₂ hM₂ pos₂ hcq _ _ W.o
  obtain ⟨ψ₀, hψ, hi, ht⟩ := hI p D G L E gb q r 𝔴 𝔴' S.atq S.sp S.std.m1 hmax hu (Ow w) S.b N₀ hcq i e he h 1 htj hint (one_mem _) M₁ M₂ c₁ c₂
    hM₁ hM₂ _ _ (T.M M₁).univ W.o W.ψ (by rw [_root_.mul_one]; exact W.trans) _ o₁ o₂ n₁ n₂
  obtain ⟨k₂, hk₂⟩ := (hQC q (datAt S.atq S.sp) (Ow w) E S.b gb M₂.1 N₀ c₂ (T.M M₂).X X₂.Y.X X₂.Y.X (T.M M₂).s X₂.Y.s X₂.Y.s
    (T.M M₂).univ X₂.Y.univ X₂.Y.univ C₂.j (𝟙 _)).2.2.2 _ (T.M M₁).s W.o W.π W.φ C₂.m
  have hb₁ : (C₁.j ≫ f) ≫ X₂.M.s = (T.M M₁).s ≫ spMap (algebraMap (Ow w) E) := by
    rw [Category.assoc, hf]
    exact C₁.ov
  have hb₂ : ((W.π ≫ C₂.j) ≫ X₂.π) ≫ X₂.M.s = (T.M M₁).s ≫ spMap (algebraMap (Ow w) E) := by
    rw [Category.assoc, Category.assoc, X₂.ov]
    refine (congrArg (W.π ≫ ·) C₂.ov).trans ?_
    simp only [← Category.assoc, W.ov]
  have hun : IsUnit ((q : ℕ) : Γ((T.M M₁).X, ⊤)) := isUnit_nat_of (T.M M₁).s q (Fact.out : q.Prime).ne_zero
  obtain ⟨y, fa, fb, ys, yt, ca, cb, sq, ms, mt⟩ := read_core hQC hO h3 hcq Tj n₁ n₂ C₁.m k₂ mf X₂.mπ hb₁ hb₂ W.ψ.left ψ₀ hψ hun hi ht
  exact ⟨⟨y, ys, by rw [yt, Category.assoc], fa, fb, ca, cb, sq, ms, by rw [mt, hk₂, Category.assoc]⟩⟩
end
