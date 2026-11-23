module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1093
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle599
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

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev
open UpperTheory.Gal.Int.Geo

namespace UpperTheory.LevelActionGenerator

variable {X : Scheme.{0}}

private theorem pb_mul {A B : Over X} [GrpObj A] [GrpObj B] {φ : A.left ⟶ B.left}
    (h : IsGrpPullback A B (𝟙 X) φ) (f : A ⟶ B) (hf : f.left = φ) {T : Over X} (x y : T ⟶ A) :
    (x * y) ≫ f = (x ≫ f) * (y ≫ f) := by
  let e : Over.mk (T.hom ≫ 𝟙 X) ≅ T := Over.isoMk (Iso.refl _) (by simp)
  have he : e.hom.left = 𝟙 _ := rfl
  have key := h.2 T x y (e.hom ≫ x ≫ f) (e.hom ≫ y ≫ f)
    (by rw [Over.comp_left, Over.comp_left, he, Category.id_comp, hf])
    (by rw [Over.comp_left, Over.comp_left, he, Category.id_comp, hf])
  rw [← MonObj.comp_mul, Over.comp_left, he, Category.id_comp] at key
  apply Over.OverMorphism.ext
  rw [key, Over.comp_left, hf]

private theorem pb_one {A B : Over X} [GrpObj A] [GrpObj B] {φ : A.left ⟶ B.left}
    (h : IsGrpPullback A B (𝟙 X) φ) (f : A ⟶ B) (hf : f.left = φ) {T : Over X} :
    (1 : T ⟶ A) ≫ f = 1 := by
  have h1 := pb_mul h f hf (1 : T ⟶ A) 1
  rw [_root_.mul_one] at h1
  simpa using h1

private theorem act_nat {O : Type} [Ring O] {A : Over X} [GrpObj A] [IsCommMonObj A] (act : OActN O A) {T : Over X}
    (u : T ⟶ A) (m : ℕ) : u ≫ act.act (m : O) = u ^ m := by
  induction m with
  | zero =>
    have h0 : act.act (0 : O) = 1 := by
      have := act.add 0 0
      rw [add_zero] at this
      simpa using this
    rw [Nat.cast_zero, h0, pow_zero, MonObj.comp_one]
  | succ m ih =>
    rw [Nat.cast_succ, act.add, act.one, MonObj.comp_mul, ih, Category.comp_id, pow_succ]

private theorem gen_mem {A : Type} [CommRing A] {a : A} {N : ℕ} {𝔞 : Ideal A} (h : IsGen a N 𝔞) : (N : A) ∈ 𝔞 := by
  have h' : (Ideal.span {a} ⊔ Ideal.span {(N : A)}) * 𝔞 = Ideal.span {(N : A)} := h
  have hm : (N : A) ∈ (Ideal.span {a} ⊔ Ideal.span {(N : A)}) * 𝔞 := by
    rw [h']
    exact Ideal.subset_span (Set.mem_singleton _)
  exact (Ideal.mul_le_right (I := Ideal.span {a} ⊔ Ideal.span {(N : A)}) (J := 𝔞)) hm

end UpperTheory.LevelActionGenerator

open UpperTheory.LevelActionGenerator in
theorem UpperTheory.quotient_level_of_lattice_generation :
    LatGen → QLev := by
  intro hLat q _ D R R' _ _ _ b gb N N₀ c a 𝔞 hN hgen X s s₀ o o₀ n
  have hw : n.φ ≫ o₀.A.hom = o.A.hom := by simpa using n.cart.1.w
  haveI : IsIso n.φ := n.cart.1.isIso_fst_of_isIso
  let f : o.A ⟶ o₀.A := Over.homMk n.φ hw
  let g : o₀.A ⟶ o.A := Over.homMk (inv n.φ) (by rw [IsIso.inv_comp_eq, hw])
  have hfl : f.left = n.φ := rfl
  have hfg : f ≫ g = 𝟙 _ := by
    apply Over.OverMorphism.ext
    simp [f, g]
  have hgf : g ≫ f = 𝟙 _ := by
    apply Over.OverMorphism.ext
    simp [f, g]
  have hinj : ∀ {T : Over X} (u v : T ⟶ o.A), u ≫ f = v ≫ f → u = v := by
    intro T u v huv
    have := congrArg (· ≫ g) huv
    simpa [Category.assoc, hfg] using this
  have hmul : ∀ {T : Over X} (u v : T ⟶ o.A), (u * v) ≫ f = (u ≫ f) * (v ≫ f) :=
    fun u v => pb_mul n.cart f hfl u v
  have hone : ∀ {T : Over X}, (1 : T ⟶ o.A) ≫ f = 1 := pb_one n.cart f hfl
  have hone' : ∀ {T : Over X}, (1 : T ⟶ o₀.A) ≫ g = 1 := by
    intro T
    apply hinj
    rw [Category.assoc, hgf, Category.comp_id, hone]
  have hact : ∀ c' : D.O, o.act.act c' ≫ f = f ≫ o₀.act.act c' := by
    intro c'
    apply Over.OverMorphism.ext
    simp only [Over.comp_left]
    exact n.act c'
  have e_add : ∀ u v : D.La, o.eta (u + v) = o.eta u * o.eta v := fun u v => o.eta_add u v
  have e_lin : ∀ (c' : D.O) (u : D.La), o.eta (c' • u) = o.eta u ≫ o.act.act c' :=
    fun c' u => o.eta_lin c' u
  have e_ker : ∀ u : D.La, o.eta (N • u) = 1 := fun u => o.eta_ker u
  obtain ⟨hL1, hL2⟩ := hLat q D a N 𝔞 hN hgen
  refine ⟨fun y => o.eta (algebraMap (𝓞 D.F) D.O a • y) ≫ f, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro y z
    simp only
    rw [smul_add, e_add, hmul]
  · intro c' y
    simp only
    have hcomm : algebraMap (𝓞 D.F) D.O a • (c' • y) = c' • (algebraMap (𝓞 D.F) D.O a • y) := by
      rw [smul_smul, smul_smul, Algebra.commutes]
    rw [hcomm, e_lin, Category.assoc, hact, Category.assoc]
  · intro y hy
    obtain ⟨z, hz⟩ := (hL1 y).2 hy
    simp only
    rw [hz, e_ker, hone]
  · intro k _ _ x
    have hβ : x ≫ s = spMap (Spec.preimage (x ≫ s)).hom := by
      simp only [spMap, CommRingCat.ofHom_hom, Spec.map_preimage]
    obtain ⟨I, hI⟩ := o.geom k x _ hβ
    have hI' : ∀ y : D.La, toUnit (Over.mk x) ≫ o.eta y = I.ev N y := fun y => hI y
    have I_add : ∀ u v : D.La, I.ev N (u + v) = I.ev N u * I.ev N v := fun u v => I.add N u v
    have I_lin : ∀ (c' : D.O) (u : D.La), I.ev N (c' • u) = I.ev N u ≫ o.act.act c' :=
      fun c' u => I.lin N c' u
    have I_ker : ∀ u : D.La, I.ev N u = 1 ↔ ∃ v : D.La, u = N • v := fun u => I.ker N hN u
    have I_onto : ∀ r : Over.mk x ⟶ o.A, r ^ N = 1 ↔ ∃ u : D.La, I.ev N u = r :=
      fun r => I.onto N hN r
    constructor
    · intro y hy
      simp only at hy
      rw [← Category.assoc, ← hone] at hy
      have h1 := hinj _ _ hy
      rw [hI'] at h1
      obtain ⟨z, hz⟩ := (I_ker _).1 h1
      exact (hL1 y).1 ⟨z, hz⟩
    · intro g₀ hg₀
      have hg'act : ∀ c' : D.O, (g₀ ≫ g) ≫ o.act.act c' = (g₀ ≫ o₀.act.act c') ≫ g := by
        intro c'
        apply hinj
        simp only [Category.assoc, hact, reassoc_of% hgf, hgf, Category.comp_id]
      have hkill : ∀ c' ∈ 𝔞, (g₀ ≫ g) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c') = 1 := by
        intro c' hc'
        rw [hg'act, hg₀ c' (by rwa [pow_one]), hone']
      have hpow : (g₀ ≫ g) ^ N = 1 := by
        have hn := act_nat o.act (g₀ ≫ g) N
        have hc : ((N : ℕ) : D.toG.O) = algebraMap (𝓞 D.F) D.O (N : 𝓞 D.F) := (map_natCast _ N).symm
        rw [hc] at hn
        rw [← hn]
        exact hkill _ (gen_mem hgen)
      obtain ⟨x', hx'⟩ := (I_onto (g₀ ≫ g)).1 hpow
      have hcond : ∀ c' ∈ 𝔞, ∃ z : D.La, algebraMap (𝓞 D.F) D.O c' • x' = N • z := by
        intro c' hc'
        apply (I_ker _).1
        rw [I_lin, hx']
        exact hkill c' hc'
      obtain ⟨y, z, hyz⟩ := hL2 x' hcond
      refine ⟨y, ?_⟩
      have hyI : toUnit (Over.mk x) ≫ o.eta (algebraMap (𝓞 D.F) D.O a • y) = g₀ ≫ g := by
        rw [hI', ← hx', hyz, I_add, (I_ker (N • z)).2 ⟨z, rfl⟩, _root_.mul_one]
      simp only
      rw [← Category.assoc, hyI, Category.assoc, hgf, Category.comp_id]
  · intro y
    rfl
end
end

section

open UpperTheory.Gal.Int.Geo
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo

private theorem inAf_mem {p : ℕ} [Fact p.Prime] (D : Datum p) (x : D.La) : inAf D x ∈ LaHat D :=
  AddSubgroup.subset_closure ⟨1, x, fun v => by rw [map_one]; exact one_mem _, rfl⟩

theorem UpperTheory.quotient_separated_of_trace_unit_crt :
    GPull → QComp → QIso → QUniq → TrEta → TrEtaPt → TrUnit → CongCRT → BaseSep := by
  intro hGP hQC hQI hQU hTE hTP hTU hCRT
  intro p _ D G L E _ _ gb w q _ r 𝔴 𝔫 S k T K₀ hLev N c a hNum C u hu W Ω _ _ z hz
  have huN : L.CongOne S.N₀ u ∧ L.CongOne S.N₀ u⁻¹ := hu
  have hu1 : u ∈ L.KN 1 := KN_anti (one_dvd _) hu
  have hInt : Integ L u := integ_of_mem hu1
  rw [hLev]
  refine ⟨hu1, ?_⟩
  rw [S.lev]
  obtain ⟨hcrt1, hcrt2⟩ := hCRT p D G L q r S.N₀ S.𝔞 S.std.cop S.upow u hInt
  rw [hcrt1]
  refine ⟨huN.1, ?_⟩
  have hNpos : 0 < (N : ℕ) := by
    have := N.2.1
    omega
  rw [hcrt2 a N hNpos N.2.2 hNum.2]
  intro y
  set x := (algebraMap (𝓞 D.F) D.O a) • y with hx
  refine (hTP p D G L E gb u (T.M N).X (T.M N).s N N (T.M N).univ W.o W.ψ W.trans Ω z x).2 rfl x ?_
  have ht : (toUnit (Over.mk z)).left = z := by
    simpa using Over.w (toUnit (Over.mk z))
  obtain ⟨oz, ⟨mz⟩⟩ := hGP _ _ gb (N : ℕ) (T.M N).X (Sp Ω) (T.M N).s z (T.M N).univ
  obtain ⟨nW, hnW⟩ := (hQC q (datAt S.atq S.sp) (Ow w) E S.b gb N S.N₀ c _ _ _ _ _ _ (T.M N).univ S.Y.univ S.Y.univ C.j (𝟙 _)).2.2.2
    _ _ W.o W.π W.φ C.m
  obtain ⟨hiso, hlb⟩ := hTU p D G L E gb u (T.M N).X (T.M N).s N N (T.M N).univ W.o W.ψ W.trans hu1
  have heta : ∀ y' : D.La, (T.M N).univ.eta (c • y') ≫ W.ψ = W.o.eta (c • y') := by
    intro y'
    refine hTE p D G L E gb u (T.M N).X (T.M N).s N N (T.M N).univ W.o W.ψ W.trans S.N₀ c c hNum.1 hNum.1
      y' y' ?_
    exact huN.1 _ (inAf_mem D y')
  obtain ⟨nI, hnI⟩ := hQI q (datAt S.atq S.sp) (Ow w) E S.b gb N N S.N₀ c c _ _ _ _ (T.M N).univ W.o S.Y.univ _ W.ψ hiso W.trans.1
    W.trans.2.1 hlb heta nW
  obtain ⟨nA, hnA⟩ := (hQC q (datAt S.atq S.sp) (Ow w) E S.b gb N S.N₀ c _ _ _ _ _ _ (T.M N).univ S.Y.univ S.Y.univ C.j (𝟙 _)).2.2.2
    _ _ oz z mz C.m
  obtain ⟨nB, hnB⟩ := (hQC q (datAt S.atq S.sp) (Ow w) E S.b gb N S.N₀ c _ _ _ _ _ _ (T.M N).univ S.Y.univ S.Y.univ (W.π ≫ C.j) (𝟙 _)).2.2.2
    _ _ oz z mz nI
  have hfeq : z ≫ W.π ≫ C.j = z ≫ C.j := hz
  have hAB : mz.φ ≫ Over.Hom.left W.ψ ≫ W.φ.φ ≫ C.m.φ = mz.φ ≫ C.m.φ := by
    generalize hF : z ≫ W.π ≫ C.j = F at nB hnB
    have hF' : F = z ≫ C.j := hF.symm.trans hfeq
    subst hF'
    have h := hQU q (datAt S.atq S.sp) (Ow w) E S.b gb N S.N₀ c S.std.three S.std.cop _ _ _ _ _ _ _ nB nA
    rw [hnB, hnI, hnW, hnA] at h
    exact h
  apply Over.OverMorphism.ext
  apply nW.cart.1.hom_ext
  · simp only [Over.comp_left, Category.assoc]
    rw [hnW, reassoc_of% (W.φ.eta x)]
    have hl := C.lv y
    have hr : Over.Hom.left ((T.M N).univ.eta x) ≫ C.m.φ = C.j ≫ Over.Hom.left (S.Y.lv y) := hl
    have hz' := mz.eta x
    rw [ht]
    rw [← reassoc_of% hz', hAB, reassoc_of% hz', hr, reassoc_of% hfeq]
  · simp only [Over.comp_left, Category.assoc, Over.w]
end

section

open UpperTheory.Gal.Int.Geo

theorem UpperTheory.tower_covering_congruence_of_hecke_lies :
    MIn → SiteEx → NumEx → ClsEx → KSCover → TjLies → KSCong := by
  intro hM hS hN hC hV hL p _ D G L hsc E _ _ e gb hstd k T N J A _ g θ w 𝔴 hpl ϑ hG
  obtain ⟨q, r, 𝔫, K₀, hat, hok, hlev, hKN, hNn, hdeck, hall⟩ := hG
  haveI : Fact q.Prime := ⟨hat.prime⟩
  haveI : 𝔴.IsMaximal := hat.max
  obtain ⟨S⟩ := hS p D G hsc E e gb hstd w q r 𝔴 𝔫 hpl hat hok
  have hNpos : 0 < N.1 := lt_of_lt_of_le (by norm_num) N.2.1
  obtain ⟨c, a, hnum⟩ := (hN p D E gb w q r 𝔴 𝔫 S N.1 hNpos).1 hNn
  obtain ⟨⟨C⟩, -⟩ := hC q (datAt S.atq S.sp) (Ow w) E S.b gb (algebraMap (Ow w) E) S.mat N.1 S.N₀ c a S.𝔞
    hnum.1 hNpos S.std.three S.std.cop hnum.2 S.Y (T.M N).X (T.M N).s (T.M N).univ
  obtain ⟨Cv⟩ := hV p D G L E gb w q r 𝔴 𝔫 S k T K₀ hlev N c a hnum C hKN J A g θ hdeck
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Ow w)
  haveI := S.et
  obtain ⟨Tc, Lc, d, h, hov, hpt⟩ := hM.cong q (datAt S.atq S.sp) (Ow w) S.f S.b S.N₀ r 𝔴 S.std S.M ϖ hϖ S.𝔞 1
    S.sup S.upow S.Y S.π S.ov inferInstance S.mπ k
  choose γ hγK hγT hγd hγr hγθ using hall
  refine ⟨Cv.toCover, q, S.f, hat.prime, S.qmem, S.norm, ϖ, fun j => (h j).corr,
    fun j => γ j (Nat.lt_succ_iff.1 j.2), fun j => (L.KN (g (γ j (Nat.lt_succ_iff.1 j.2))).M.1).relIndex
      (K₀ ⊓ K₀.comap (MulAut.conj (g (γ j (Nat.lt_succ_iff.1 j.2))).h).toMonoidHom), hϖ, hpt, fun j => ⟨hov j, ?_, ?_⟩⟩
  · obtain ⟨h0, κ, e1, e2, e3⟩ := hL p D G L E gb w q r 𝔴 𝔫 S k T K₀ hlev N c a hnum C hKN J g _ j
      (Nat.lt_succ_iff.1 j.2) (hγK _ _) (hγT _ _) (hγd _ _) (hγr _ _) (Tc j) (Lc j)
    exact ⟨h0, κ, e1, e2, e3⟩
  · exact hγθ _ _
end

section

open UpperTheory.Gal.Int.Geo
open CategoryTheory AlgebraicGeometry

private theorem powMap_congr {S' S : Scheme.{0}} {A' : Over S'} {A : Over S} {f f' : S' ⟶ S} {φ φ' : A'.left ⟶ A.left}
    (hf : f = f') (hφ : φ = φ') (h : φ ≫ A.hom = A'.hom ≫ f) (h' : φ' ≫ A.hom = A'.hom ≫ f') (k : ℕ) :
    GlobalTheory.KS.powMap f φ h k = GlobalTheory.KS.powMap f' φ' h' k := by
  subst hf hφ
  rfl

theorem UpperTheory.tower_invariant_of_base_invariant_powerCartesian :
    BaseInv → PowCart → PiInv := by
  intro hB hP p _ D G L E _ _ gb w q _ r 𝔴 𝔫 S k T K₀ hK N' N t c a hN hNum C' C u hu x y
  obtain ⟨π, o, ψ, φ, hw, ov, tr, e⟩ := T.tr_eq N' N u x y
  obtain ⟨h1, h2⟩ := hB p D G L E gb w q r 𝔴 𝔫 S k T K₀ hK N' N t c a hN hNum C' C u hu
    ⟨π, o, ψ, φ, ov, tr⟩
  have h1' : π ≫ C.j = C'.j := h1
  have h2' : (ψ.left ≫ φ.φ) ≫ C.m.φ = C'.m.φ := by
    rw [Category.assoc]; exact h2
  have hv := C.m.cart.1.w
  have hw' : ((ψ.left ≫ φ.φ) ≫ C.m.φ) ≫ S.Y.univ.A.hom = (T.M N').univ.A.hom ≫ π ≫ C.j := by
    rw [Category.assoc, hv, ← Category.assoc, hw, Category.assoc]
  have hc := (hP _ _ _ (T.M N').univ.A (T.M N).univ.A S.Y.univ.A π C.j (ψ.left ≫ φ.φ) C.m.φ hw hv k).2.2 hw'
  simp only [Site.pi, Cls.pw]
  rw [← Category.assoc, e, Category.assoc, hc]
  exact congrArg _ (powMap_congr h1' h2' _ _ k)
end

section

open UpperTheory.Gal.Int.Geo

theorem UpperTheory.tower_point_count_statement :
    Count := by
  intro Γ _ K₀ H K hKH hHK₀ hK F κ hF hκ ζ
  classical
  have hmul : K.relIndex H * H.relIndex K₀ = K.relIndex K₀ :=
    Subgroup.relIndex_mul_relIndex K H K₀ hKH hHK₀
  have hKH0 : K.relIndex H ≠ 0 := fun h0 => hK (by rw [← hmul, h0, zero_mul])
  have hH0 : H.relIndex K₀ ≠ 0 := fun h0 => hK (by rw [← hmul, h0, mul_zero])
  haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; exact hH0)
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Finite (↥K₀ ⧸ K.subgroupOf K₀) := Nat.finite_of_card_ne_zero hK
  haveI : Finite (↥H ⧸ K.subgroupOf H) := Nat.finite_of_card_ne_zero hKH0
  have bound : ∀ ξ : F, Nat.card {x // κ x = ξ} ≤ K.relIndex H := by
    intro ξ
    by_cases hne : Nonempty {x // κ x = ξ}
    · obtain ⟨⟨q0, hq0⟩⟩ := hne
      have memH : ∀ q : {x // κ x = ξ},
          ((q0.out : ↥K₀) : Γ)⁻¹ * ((q.1.out : ↥K₀) : Γ) ∈ H := by
        intro q
        apply hκ
        rw [QuotientGroup.out_eq', QuotientGroup.out_eq', hq0, q.2]
      let f : {x // κ x = ξ} → ↥H ⧸ K.subgroupOf H := fun q => ((⟨_, memH q⟩ : ↥H) : ↥H ⧸ K.subgroupOf H)
      have hinj : Function.Injective f := by
        intro q1 q2 h12
        have h' := QuotientGroup.eq.mp h12
        rw [Subgroup.mem_subgroupOf] at h'
        apply Subtype.ext
        rw [← QuotientGroup.out_eq' q1.1, ← QuotientGroup.out_eq' q2.1]
        apply QuotientGroup.eq.mpr
        rw [Subgroup.mem_subgroupOf]
        simpa [mul_assoc] using h'
      calc Nat.card {x // κ x = ξ} ≤ Nat.card (↥H ⧸ K.subgroupOf H) :=
            Nat.card_le_card_of_injective f hinj
        _ = K.relIndex H := rfl
    · haveI := not_nonempty_iff.mp hne
      rw [Nat.card_of_isEmpty]
      exact Nat.zero_le _
  have hsum : ∑ ξ : F, Nat.card {x // κ x = ξ} = ∑ ξ : F, K.relIndex H := by
    rw [← Nat.card_sigma, Nat.card_congr (Equiv.sigmaFiberEquiv κ), Finset.sum_const,
      Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card, hF, mul_comm, hmul]
    rfl
  exact (Finset.sum_eq_sum_iff_of_le (fun ξ _ => bound ξ)).mp hsum ζ (Finset.mem_univ _)
end

section

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo

theorem UpperTheory.trace_eta_pointwise : TrEtaPt := by
  intro p _ D G L R _ _ gb h X s N' N o' o ψ hT Ω _ _ z x
  obtain ⟨-, -, -, -, hgeo⟩ := hT
  have hz : z ≫ s = spMap (Spec.preimage (z ≫ s)).hom := by
    simp [spMap, Spec.map_preimage]
  obtain ⟨I', I'', h1, h2, h3⟩ := hgeo Ω z _ hz
  have hpos : ∀ M : Lv p, 0 < (M : ℕ) := fun M => by
    have := M.2.1
    omega
  have hzero : ∀ n : ℕ, I''.ev n 0 = 1 := fun n => by
    have h := I''.add n 0 0
    rw [add_zero] at h
    exact (mul_eq_left.mp h.symm)
  have hin0 : inAf D 0 = 0 := by
    simp [inAf]
  have e1 := congrArg (· ≫ ψ) (h1 x)
  simp only [Category.assoc] at e1
  refine ⟨?_, ?_⟩
  · refine Iff.trans ?_ ((h3 _ (hpos N') N'.2.2 x 0).trans ?_)
    · rw [e1]
      first
        | simp only [hzero]
        | erw [hzero]
    · simp only [hin0, zero_add]
  · rintro rfl y hxy
    refine (h3 _ (hpos N') N'.2.2 x y).mp ?_
    rw [← e1, hxy]
    exact h2 y
end
end

section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open UpperTheory.Gal.Int.Geo

private theorem unit_aux {A : Type} [CommRing A] {m c t t' s : A} (hm : m = c * t) (ht : t * t' = 1)
    (hs : m * s = 1) : c = 1 * (m * t') ∧ (m * t') * (t * s) = 1 := by
  constructor
  · rw [_root_.one_mul, hm, _root_.mul_assoc, ht, _root_.mul_one]
  · calc (m * t') * (t * s) = (m * s) * (t * t') := by ring
      _ = 1 := by rw [hs, ht, _root_.one_mul]

theorem UpperTheory.trace_unit_of_pullback_multiplier :
    TrBack → MultUnit → TrUnit := by
  intro hB hM p _ D G L R _ _ gb h X s N' N o' o ψ hT hh
  obtain ⟨ψ', -, e₁, e₂⟩ := hB p D G L R gb h X s N' N o' o ψ hT 1 (Nat.coprime_one_left p)
    (fun v hv => ⟨L.actG h⁻¹ v, integ_of_mem (inv_mem hh) v hv, by
      rw [one_smul, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]⟩)
  have hiso : CategoryTheory.IsIso ψ := ⟨ψ', e₁.trans (pow_one _), e₂.trans (pow_one _)⟩
  refine ⟨hiso, ?_⟩
  obtain ⟨-, -, -, ⟨c, hc, hP, t, t', ht, ht', htt, hm⟩, -⟩ := hT
  obtain ⟨hu, hfix⟩ := hM p D G L
  obtain ⟨s', hi, hs, hs1⟩ := hu h hh
  obtain ⟨a₁, a₂⟩ := unit_aux hm htt hs1
  have hint : ∀ {a b : GlobalTheory.LKTrip.AfP p}, GlobalTheory.LKGeo.IsIntAf a → GlobalTheory.LKGeo.IsIntAf b → GlobalTheory.LKGeo.IsIntAf (a * b) := fun ha hb v => by
    rw [map_mul]; exact mul_mem (ha v) (hb v)
  have hc1 : c = 1 := hfix c 1 _ _ hc (Nat.coprime_one_left p) (hint hi ht') (hint ht hs) a₂
    (by rw [Nat.cast_one]; exact a₁)
  subst hc1
  exact hP
end

section

open UpperTheory.Gal.Int.Geo

private theorem matrix_unique_algEquiv (R A m : Type) [CommSemiring R] [Semiring A] [Algebra R A]
    [fm : Fintype m] [dm : DecidableEq m] [Unique m] : Nonempty (Matrix m m A ≃ₐ[R] A) := by
  refine ⟨{ toFun := fun M => M default default
            invFun := fun a => Matrix.of fun _ _ => a
            left_inv := ?_
            right_inv := ?_
            map_mul' := ?_
            map_add' := ?_
            commutes' := ?_ }⟩
  · intro M
    ext i j
    simp [Subsingleton.elim i default, Subsingleton.elim j default]
  · intro a
    simp
  · intro M N
    simp [Matrix.mul_apply]
  · intro M N
    simp
  · intro r
    simp [Matrix.algebraMap_matrix_apply]

open scoped TensorProduct in
theorem UpperTheory.rational_splitting_exists :
    SplitQ := by
  intro p _ D hm q _
  haveI : Unique (Fin D.m) :=
    { default := ⟨0, by omega⟩
      uniq := fun i => Fin.ext (by have := i.2; simp; omega) }
  let e0 : D.O ≃ₐ[NumberField.RingOfIntegers D.F] NumberField.RingOfIntegers D.F :=
    (AlgEquiv.ofBijective (Algebra.ofId _ _)
      ⟨D.algebraMap_injective hm, GlobalTheory.T.integers_surjective_of_rank_one p D hm⟩).symm
  exact ⟨(Algebra.TensorProduct.congr e0 AlgEquiv.refl).trans
    (matrix_unique_algEquiv _ _ _).some.symm⟩
end

section

open UpperTheory.Gal.Int.Geo
open CategoryTheory

theorem UpperTheory.power_map_cartesian :
    PowCart := by
  intro X Y Z A B C f g φ χ u v k
  refine ⟨fun H => GlobalTheory.KS.PowPB.powMap_isPullback _ _ _ _ f φ u H k,
    GlobalTheory.KS.PowPB.powMap_w f φ u k, fun w => ?_⟩
  apply GlobalTheory.KS.PowPB.pow_left_hom_ext
  · rw [Category.assoc, GlobalTheory.KS.PowPB.powMap_w, ← Category.assoc, GlobalTheory.KS.PowPB.powMap_w,
      Category.assoc, GlobalTheory.KS.PowPB.powMap_w]
  · intro i
    rw [Category.assoc, GlobalTheory.KS.PowPB.powMap_pr, ← Category.assoc, GlobalTheory.KS.PowPB.powMap_pr,
      Category.assoc, GlobalTheory.KS.PowPB.powMap_pr]
end
