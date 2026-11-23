module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle020
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsoEqOfMapsAlongSection
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle031
import Formalism.LocalToGlobal.ProjectiveLattices.ThetaFramePf
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle029
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle019
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle033
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle017
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.KeyFormulaPowOfKeyFormula
public import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementB
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle032
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Formalism.LocalToGlobal.CMDeterminantIdeals.DetIdeal
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm

@[expose] public section

section



noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT.TieCalc

theorem isoMaps_iff {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F))
    (σ : LB.Sec L') (s : LB.Sec (L.pull F)) :
    IsoMaps w σ s ↔ ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (j : L.ι) (k : L'.ι), F (r z) ∈ L.U j → r z ∈ L'.U k →
      gs r z _ (s.f (fun _ => j)) = (gw w r z j k).val * gs r z _ (σ.f k) := by
  constructor
  · intro h Z r z j k hj hk
    have hz : r z ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
    have a := congrArg (gs r z _) (h (fun _ => j) k)
    exact (gs_res _ z _ hz _).symm.trans (a.trans ((gs_mul _ z _ hz _ _).trans
        (congrArg₂ (· * ·) (gs_unit _ z _ hz _) (gs_res _ z _ hz _))))
  · intro h (i : PUnit → L.ι) k
    exact fn_ext fun p hp =>
      (gs_res _ p _ hp _).trans ((h _ (𝟙 _) p (i PUnit.unit) k (mem_pull.1 hp.1) hp.2).trans
        (Eq.symm ((gs_mul _ p _ hp _ _).trans (congrArg₂ (· * ·) (gs_unit (𝟙 _) p _ hp _) (gs_res _ p _ hp _)))))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {t : SAB H (Sp S)} (m : SABMap t Xo.univ.t x)

theorem exists_canon : ∃ g : t.G.left ⟶ Gx x, g ≫ (snd (Over.mk x) Xo.univ.t.G).left = m.φ ∧
    g ≫ (fst (Over.mk x) Xo.univ.t.G).left = t.G.hom := by
  let a₀ : Over.mk (t.G.hom ≫ x) ⟶ Over.mk x := Over.homMk t.G.hom rfl
  let b₀ : Over.mk (t.G.hom ≫ x) ⟶ Xo.univ.t.G := Over.homMk m.φ m.cart.1.w
  exact ⟨(lift a₀ b₀).left, congrArg (fun q => q.left) (lift_snd a₀ b₀), congrArg (fun q => q.left) (lift_fst a₀ b₀)⟩

theorem canon_mem {g : t.G.left ⟶ Gx x} (hg : g ≫ (snd (Over.mk x) Xo.univ.t.G).left = m.φ)
    (j : Xo.univ.t.PP.L.ι) (y : t.G.left) (hy : m.φ y ∈ Xo.univ.t.PP.L.U j) : g y ∈ (PPx x).U (fun _ => j) :=
  Set.mem_iInter.2 fun _ => (congrArg (fun q => q y ∈ Xo.univ.t.PP.L.U j) hg).mpr hy

theorem rigIso_unique {w w' : LB.Iso t.PP.L (Xo.univ.t.PP.L.pull m.φ)} (h : RigIso m w) (h' : RigIso m w') :
    w = w' := by
  have hp : IsProper t.G.hom := MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 Xo.univ.proper
  have hab : IsAbelianScheme t.G := ⟨t.semi.comm, t.semi.smooth, hp, t.semi.geomConnected⟩
  exact GlobalTheory.iso_eq_of_maps_along_section (S := Sp S) (exists_chart t.PP.isLB)
    (fun y => (exists_chart Xo.univ.t.PP.isLB (m.φ y)).elim fun j hj => ⟨fun _ => j, mem_pull.2 hj⟩)
    t.G.hom (eSec t.G) (Over.w η[t.G]) (GlobalTheory.globalFns_holds _ _ hab).2 h.1 h'.1 h.2 h'.2

theorem secTie_iff {w : LB.Iso t.PP.L (Xo.univ.t.PP.L.pull m.φ)} (hw : RigIso m w) {g : t.G.left ⟶ Gx x}
    (hs : g ≫ (snd (Over.mk x) Xo.univ.t.G).left = m.φ) (hf : g ≫ (fst (Over.mk x) Xo.univ.t.G).left = t.G.hom)
    (th : LB.Sec t.PP.L) (s : LB.Sec (PPx x)) :
    SecTie m th s ↔ ∀ (Z : Scheme.{0}) (r : Z ⟶ t.G.left) (z : Z) (j : Xo.univ.t.PP.L.ι) (k : t.PP.L.ι),
      m.φ (r z) ∈ Xo.univ.t.PP.L.U j → r z ∈ t.PP.L.U k →
      gs (r ≫ g) z ((PPx x).U (fun _ => j)) (s.f (fun _ => j)) = (gw w r z j k).val * gs r z _ (th.f k) := by
  constructor
  · rintro ⟨w', s1, r1, i1, c⟩ Z r z j k hj hk
    obtain rfl : w' = w := rigIso_unique m r1 hw
    have le : (Xo.univ.t.PP.L.pull m.φ).U (fun _ => j) ≤ g ⁻¹ᵁ (PPx x).U (fun _ => j) :=
      fun q hq => canon_mem m hs j q (mem_pull.1 hq)
    refine Eq.trans ?_ ((isoMaps_iff w' th s1).1 i1 Z r z j k hj hk)
    rw [c g hs hf (fun _ => j) le]
    exact (gs_appLE g _ _ le r z (mem_pull.2 hj) _).symm
  · intro a
    obtain ⟨s1, hs1⟩ := thf_secUp ((isGen_iff w).1 hw.1) Xo.univ.t.PP.isLB t.PP.isLB th
    refine ⟨w, s1, hw, (isoMaps_iff w th s1).2 fun Z r z j k hj hk => hs1 Z r z (fun _ => j) k (mem_pull.2 hj) hk, ?_⟩
    intro g' e₁ e₂ (J : PUnit → Xo.univ.t.PP.L.ι) hJ
    obtain rfl : g' = g := SecCalc.pm_ext _ _ (e₁.trans hs.symm) (e₂.trans hf.symm)
    refine fn_ext fun p hp => ?_
    obtain ⟨k, hk⟩ := exists_chart t.PP.isLB p
    rw [hs1 _ (𝟙 _) p J k hp hk, gs_appLE _ _ _ hJ (𝟙 _) p hp, a _ (𝟙 _) p _ k (mem_pull.1 hp) hk]

theorem secTie_scale {th th' : LB.Sec t.PP.L} {s s' : LB.Sec (PPx x)} (h : SecTie m th s) (a : S)
    (hs' : ∀ i, s'.f i = scal x a i * s.f i) :
    SecTie m th' s' ↔ ∀ i, th'.f i = constFn t.G.hom _ a * th.f i := by
  obtain ⟨g, hs, hf⟩ := exists_canon m
  obtain ⟨w, -, hw, -⟩ := id h
  rw [secTie_iff m hw hs hf] at h ⊢
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ t.G.left) (z : Z) (j : Xo.univ.t.PP.L.ι) (k : t.PP.L.ι),
      m.φ (r z) ∈ Xo.univ.t.PP.L.U j → r z ∈ t.PP.L.U k →
      gs (r ≫ g) z ((PPx x).U (fun _ => j)) (s'.f (fun _ => j)) =
        (gw w r z j k).val * gs r z _ (constFn t.G.hom _ a * th.f k) := by
    intro Z r z j k hj hk
    have a₁ : (r ≫ g) z ∈ (PPx x).U (fun _ => j) := canon_mem m hs j _ hj
    rw [gs_mul _ z _ hk, gs_constFn _ _ _ z hk, mul_left_comm]
    refine (congrArg (gs _ z _) (hs' _)).trans ((gs_mul _ z _ a₁ _ _).trans (congrArg₂ (· * ·) ?_ (h Z r z j k hj hk)))
    exact (gs_constFn (fst (Over.mk x) Xo.univ.t.G).left _ _ z a₁ a).trans (by rw [Category.assoc, hf])
  constructor
  · intro h' k
    refine fn_ext fun y hy => ?_
    obtain ⟨j, hj⟩ := exists_chart Xo.univ.t.PP.isLB (m.φ y)
    exact (Units.mul_right_inj _).1 ((h' _ (𝟙 _) y j k hj hy).symm.trans (key _ (𝟙 _) y j k hj hy))
  · intro h' Z r z j k hj hk
    rw [h' k]
    exact key Z r z j k hj hk

theorem secTie_baseChange {th : LB.Sec t.PP.L} {s : LB.Sec (PPx x)} (h : SecTie m th s) {S' : Type} [CommRing S']
    (φ : S →+* S') {x' : Sp S' ⟶ Xo.X} {t'' : SAB H (Sp S')} (m' : SABMap t'' Xo.univ.t x')
    (n : SABMap t'' t (spMap φ)) (s' : LB.Sec (PPx x')) (w : LB.Iso t''.PP.L (t.PP.L.pull n.φ))
    (θ : LB.Sec (t.PP.L.pull n.φ)) (th' : LB.Sec t''.PP.L) (hx : x' = spMap φ ≫ x) (hφ : m'.φ = n.φ ≫ m.φ)
    (hb : SecBC φ 1 x x' s s') (hw : RigIso n w) (hθ : PullSec n.φ th θ) :
    SecTie m' th' s' ↔ IsoMaps w th' θ := by
  obtain ⟨g, hs, hf⟩ := exists_canon m
  obtain ⟨g', hs', hf'⟩ := exists_canon m'
  obtain ⟨w₁, -, hw₁, -⟩ := id h
  obtain ⟨w₂, hw₂, T⟩ := GlobalTheory.LiftBaseChange.rigIso_comp m n m' hx hφ hw₁ hw
  obtain ⟨pm, ps, pf, hp⟩ := hb
  have eg : g' ≫ pm = n.φ ≫ g := by
    apply SecCalc.pm_ext
    · rw [Category.assoc, ps, hs', Category.assoc, hs, hφ]
    · rw [Category.assoc, pf, ← Category.assoc, hf', Category.assoc, hf]
      exact n.cart.1.w.symm
  have ept : ∀ y, m'.φ y = m.φ (n.φ y) := fun y => by rw [hφ]; rfl
  rw [secTie_iff m hw₁ hs hf] at h
  rw [secTie_iff m' hw₂ hs' hf', isoMaps_iff]
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ t''.G.left) (z : Z) (j : Xo.univ.t.PP.L.ι) (i : t.PP.L.ι),
      m.φ (n.φ (r z)) ∈ Xo.univ.t.PP.L.U j → n.φ (r z) ∈ t.PP.L.U i →
      gs (r ≫ g') z ((PPx x').U (fun _ => j)) (s'.f (fun _ => j)) =
        (gw w₁ (r ≫ n.φ) z j i).val * gs r z _ (θ.f (fun _ => i)) := by
    intro Z r z j i hj hi
    have a₁ : (r ≫ g') z ∈ (PPx x').U (fun _ => j) := canon_mem m' hs' j _ (by rw [ept]; exact hj)
    have le : (t.PP.L.pull n.φ).U (fun _ => i) ≤ n.φ ⁻¹ᵁ t.PP.L.U i := fun q hq => mem_pull.1 hq
    have e₁ := hp (fun _ => j) (SecCalc.ppx_le pm ps _)
    rw [SecCalc.scal_one' x (fun _ => j), _root_.one_mul] at e₁
    rw [hθ (fun _ => i) le, gs_appLE n.φ _ _ le r z (mem_pull.2 hi), ← h Z (r ≫ n.φ) z j i hj hi, ← e₁,
      gs_appLE pm _ _ _ (r ≫ g') z a₁, Category.assoc, Category.assoc, eg]
  constructor
  · intro h' Z r z i k hi hk
    obtain ⟨j, hj⟩ := exists_chart Xo.univ.t.PP.isLB (m.φ (n.φ (r z)))
    have e := (key Z r z j i hj hi).symm.trans (h' Z r z j k (by rw [ept]; exact hj) hk)
    rw [T Z r z j i k hj hi hk, Units.val_mul, _root_.mul_assoc] at e
    exact (Units.mul_right_inj _).1 e
  · intro h' Z r z j k hj hk
    obtain ⟨i, hi⟩ := exists_chart t.PP.isLB (n.φ (r z))
    rw [ept] at hj
    rw [key Z r z j i hj hi, h' Z r z i k hi hk, T Z r z j i k hj hi hk, Units.val_mul, _root_.mul_assoc]

theorem secTie_calc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (t' : SAB H (Sp S)) (m : SABMap t' Xo.univ.t x) (th : LB.Sec t'.PP.L) (s : LB.Sec (PPx x)), SecTie m th s → (∀ (a : S) (x' : Sp S ⟶ Xo.X) (s' : LB.Sec (PPx x')) (th' : LB.Sec t'.PP.L), x' = x → SecBC (RingHom.id S) a x x' s s' → (SecTie m th' s' ↔ ∀ i, th'.f i = constFn t'.G.hom _ a * th.f i)) ∧ ∀ (S' : Type) [CommRing S'] (φ : S →+* S') (x' : Sp S' ⟶ Xo.X) (t'' : SAB H (Sp S')) (m' : SABMap t'' Xo.univ.t x') (n : SABMap t'' t' (spMap φ)) (s' : LB.Sec (PPx x')) (w : LB.Iso t''.PP.L (t'.PP.L.pull n.φ)) (θ : LB.Sec (t'.PP.L.pull n.φ)) (th' : LB.Sec t''.PP.L), x' = spMap φ ≫ x → m'.φ = n.φ ≫ m.φ → SecBC φ 1 x x' s s' → RigIso n w → PullSec n.φ th θ → (SecTie m' th' s' ↔ IsoMaps w th' θ) := by
  intro E _ _ _ H Dw l Xo S _ x t' m th s h
  refine ⟨fun a x' s' th' hx hb => ?_, fun S' _ φ x' t'' m' n s' w θ th' hx hφ hb hw hθ =>
    secTie_baseChange m h φ m' n s' w θ th' hx hφ hb hw hθ⟩
  subst hx
  have e : x' = spMap (RingHom.id S) ≫ x' := by rw [SecCalc.spMap_id', Category.id_comp]
  exact secTie_scale m h a
    (((SecCalc.sec_calc E H Dw l Xo S S S (RingHom.id S) (RingHom.id S) x' x' x' e e).2.1 a s s').1 hb)

end GlobalTheory.LamT.TieCalc
end
end

section

open NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CM

open GlobalTheory.HostModel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


omit [IsCMField E] in
theorem int_dvd_of_mul_eq_ringOfIntegers {N m : ℤ} {z : 𝓞 E} (h : (N : 𝓞 E) * z = m) : N ∣ m := by
  have h1 : algebraMap ℤ (𝓞 E) N ∣ algebraMap ℤ (𝓞 E) m := ⟨z, by simpa using h.symm⟩
  have h2 := map_dvd (Algebra.norm ℤ) h1
  rw [Algebra.norm_algebraMap, Algebra.norm_algebraMap] at h2
  exact (Int.pow_dvd_pow_iff Module.finrank_pos.ne').1 h2

theorem int_dvd_of_sq_dvd_squarefree_mul_sq {d N v : ℤ} (hd : Squarefree d) (hN : N ≠ 0)
    (h : N ^ 2 ∣ d * v ^ 2) : N ∣ v := by
  obtain ⟨N', v', h1, h2, h3⟩ := extract_gcd N v
  generalize gcd N v = g at h1 h2
  subst h1 h2
  have hg : g ≠ 0 := left_ne_zero_of_mul hN
  have h4 : N' ^ 2 ∣ d * v' ^ 2 := by
    rw [mul_pow, mul_pow, mul_left_comm] at h
    exact (mul_dvd_mul_iff_left (pow_ne_zero 2 hg)).1 h
  have hc : IsCoprime N' v' := (gcd_isUnit_iff _ _).1 h3
  have h5 : N' * N' ∣ d := by
    rw [← sq]
    exact (hc.pow (m := 2) (n := 2)).dvd_of_dvd_mul_right h4
  exact mul_dvd_mul_left g (hd _ h5).dvd

theorem cm_generator_sq_quadratic_eq (H : Host E) : H.w0 ^ 2 + (((1 + H.d) / 4 : ℕ) : 𝓞 E) = H.w0 := by
  have h4 : 4 * ((1 + H.d) / 4) = 1 + H.d := by have := H.d_mod; omega
  have h5 : (4 : 𝓞 E) * (((1 + H.d) / 4 : ℕ) : 𝓞 E) = 1 + H.d := by exact_mod_cast congrArg (Nat.cast : ℕ → 𝓞 E) h4
  have h := H.rt_sq
  rw [rt_eq] at h
  apply mul_left_cancel₀ (show (4 : 𝓞 E) ≠ 0 by norm_num)
  linear_combination h + h5

theorem exists_coord (H : Host E) {a : 𝓞 E} (ha : a ∈ OK H) : ∃ u v : ℤ, a = u + v * H.w0 := by
  first
  | exact @_root_.GlobalTheory.CMGeneratorSquare.main
  | exact _root_.GlobalTheory.CMGeneratorSquare.main
  | (apply _root_.GlobalTheory.CMGeneratorSquare.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.CMGeneratorSquare.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CMGeneratorSquare.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CMGeneratorSquare.main ..)

theorem coord_eq_zero (H : Host E) {u v : ℤ} (h : (u : 𝓞 E) + v * H.w0 = 0) : u = 0 ∧ v = 0 := by
  have h1 := congrArg H.bar h
  rw [map_add (f := _), map_mul, map_intCast, map_intCast, cmHost_bar_halfIntegerGenerator, map_zero] at h1
  have h2 : (v : 𝓞 E) * H.rt = 0 := by rw [rt_eq]; linear_combination h - h1
  have h3 : v = 0 := by exact_mod_cast (mul_eq_zero.1 h2).resolve_right (rt_ne_zero H)
  subst h3
  exact ⟨by simpa using h, rfl⟩

theorem coord_mem (H : Host E) (u v : ℤ) : (u : 𝓞 E) + v * H.w0 ∈ OK H :=
  add_mem (intCast_mem _ u) (mul_mem (intCast_mem _ v) (Algebra.self_mem_adjoin_singleton ℤ _))

theorem coord_mul_bar (H : Host E) (u v : ℤ) : ((u : 𝓞 E) + v * H.w0) * H.bar (u + v * H.w0) =
    ((u ^ 2 + u * v + ((1 + H.d) / 4 : ℕ) * v ^ 2 : ℤ) : 𝓞 E) := by
  have h := cm_generator_sq_quadratic_eq H
  generalize (1 + H.d) / 4 = k at h
  rw [map_add (f := _), map_mul, map_intCast, map_intCast, cmHost_bar_halfIntegerGenerator]
  push_cast
  linear_combination (-v ^ 2 : 𝓞 E) * h

theorem mem_OK_of_int_mul_mem (H : Host E) {N : ℤ} (hN : N ≠ 0) {y : 𝓞 E} (hy : (N : 𝓞 E) * y ∈ OK H) :
    y ∈ OK H := by
  obtain ⟨u, v, h⟩ := exists_coord H hy
  have hb := congrArg H.bar h
  have hn := coord_mul_bar H u v
  rw [← h, map_mul, map_intCast] at hn
  rw [map_mul, map_add (f := _), map_mul, map_intCast, map_intCast, map_intCast, cmHost_bar_halfIntegerGenerator] at hb
  have h1 : N ∣ 2 * u + v :=
    int_dvd_of_mul_eq_ringOfIntegers (z := y + H.bar y) (by push_cast; linear_combination h + hb)
  have h2 : N ^ 2 ∣ u ^ 2 + u * v + ((1 + H.d) / 4 : ℕ) * v ^ 2 :=
    int_dvd_of_mul_eq_ringOfIntegers (z := y * H.bar y) (by rw [← hn]; push_cast; ring)
  have h4 : (4 : ℤ) * ((1 + H.d) / 4 : ℕ) = 1 + H.d := by have := H.d_mod; omega
  have h3 : N ^ 2 ∣ H.d * v ^ 2 := by
    have := dvd_sub (h2.mul_left 4) (pow_dvd_pow_of_dvd h1 2)
    rwa [show 4 * (u ^ 2 + u * v + ((1 + H.d) / 4 : ℕ) * v ^ 2) - (2 * u + v) ^ 2 = H.d * v ^ 2 by
      linear_combination v ^ 2 * h4] at this
  obtain ⟨v', rfl⟩ := int_dvd_of_sq_dvd_squarefree_mul_sq
    (Int.squarefree_natCast.2 H.d_prime.squarefree) hN h3
  obtain ⟨u', rfl⟩ : N ∣ u :=
    int_dvd_of_mul_eq_ringOfIntegers (z := y - (v' : 𝓞 E) * H.w0) (by push_cast at h; linear_combination h)
  have : y = u' + v' * H.w0 :=
    mul_left_cancel₀ (show (N : 𝓞 E) ≠ 0 by exact_mod_cast hN) (by push_cast at h; linear_combination h)
  rw [this]
  exact coord_mem H u' v'

theorem finite_int_OK (H : Host E) : Module.Finite ℤ (OK H) :=
  Module.Finite.of_injective (OK H).val.toLinearMap Subtype.val_injective

theorem isIntegrallyClosed_OK (H : Host E) : IsIntegrallyClosed (OK H) := by
  have := finite_int_OK H
  rw [isIntegrallyClosed_iff (FractionRing (OK H))]
  intro x hx
  have hinj : Function.Injective (algebraMap (OK H) E) :=
    RingOfIntegers.coe_injective.comp Subtype.val_injective
  let φ : FractionRing (OK H) →ₐ[OK H] E :=
    IsFractionRing.liftAlgHom (g := Algebra.ofId (OK H) E) hinj
  have hy : IsIntegral ℤ (φ x) := isIntegral_trans _ (hx.map φ)
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := OK H) x
  obtain ⟨n, hn, c, hc⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) b).exists_nonzero_dvd hb
  have hb' : algebraMap (OK H) E b ≠ 0 := (map_ne_zero_iff _ hinj).2 (nonZeroDivisors.ne_zero hb)
  have hm : (⟨_, hy⟩ : 𝓞 E) ∈ OK H := by
    refine mem_OK_of_int_mul_mem H hn ?_
    convert (a * c).2 using 1
    apply RingOfIntegers.coe_injective
    have h1 : (n : E) = algebraMap (OK H) E b * algebraMap (OK H) E c := by
      rw [← map_mul, ← hc]; simp
    change (n : E) * φ _ = algebraMap (OK H) E (a * c)
    rw [map_div₀, φ.commutes, φ.commutes, h1, map_mul]
    field_simp
  refine ⟨⟨_, hm⟩, φ.injective ?_⟩
  exact φ.commutes _

theorem isDedekindDomain_OK (H : Host E) : IsDedekindDomain (OK H) :=
  have := finite_int_OK H
  { isNoetherian_of_tower ℤ (inferInstance : IsNoetherian ℤ (OK H)),
    Ring.DimensionLEOne.of_isIntegral ℤ (OK H), isIntegrallyClosed_OK H with }

theorem existsUnique_coord (H : Host E) (a : OK H) :
    ∃! m : ℤ × ℤ, a = (m.1 : OK H) + (m.2 : OK H) * wK H := by
  obtain ⟨u, v, h⟩ := exists_coord H a.2
  refine ⟨(u, v), Subtype.ext h, ?_⟩
  rintro ⟨u', v'⟩ h'
  have h2 : (a : 𝓞 E) = u' + v' * H.w0 := congrArg Subtype.val h'
  obtain ⟨h3, h4⟩ := coord_eq_zero H (u := u' - u) (v := v' - v) (by push_cast; linear_combination h - h2)
  exact Prod.ext (sub_eq_zero.1 h3) (sub_eq_zero.1 h4)

theorem finrank_int_OK (H : Host E) : Module.finrank ℤ (OK H) = 2 := by
  let f : (ℤ × ℤ) →ₗ[ℤ] OK H := LinearMap.coprod (LinearMap.toSpanSingleton ℤ _ 1)
    (LinearMap.toSpanSingleton ℤ _ (wK H))
  have hf : Function.Bijective f := by
    rw [Function.bijective_iff_existsUnique]
    intro a
    simpa [f, eq_comm (a := a)] using existsUnique_coord H a
  rw [← (LinearEquiv.ofBijective f hf).finrank_eq]
  simp

def barOK (H : Host E) : OK H ≃+* OK H where
  toFun a := ⟨H.bar a, LevelExist.bar_mem_adjoin H a.2⟩
  invFun a := ⟨H.bar a, LevelExist.bar_mem_adjoin H a.2⟩
  left_inv a := Subtype.ext (bar_bar H a)
  right_inv a := Subtype.ext (bar_bar H a)
  map_mul' a b := Subtype.ext (map_mul H.bar _ _)
  map_add' a b := Subtype.ext (map_add H.bar _ _)

theorem two_mul_finrank_OK (H : Host E) (M : Type) [AddCommGroup M] [Module (𝓞 E) M] [Module.Finite (𝓞 E) M] :
    2 * Module.finrank (OK H) M = Module.finrank ℚ E * Module.finrank (𝓞 E) M := by
  have := finite_int_OK H
  have : Module.Finite ℤ M := Module.Finite.trans (𝓞 E) M
  have : Module.Finite (OK H) M := Module.Finite.of_restrictScalars_finite ℤ _ _
  rw [← finrank_int_OK H, ← finrank_int_eq_mul_of_finite, ← RingOfIntegers.rank,
    ← finrank_int_eq_mul_of_finite]

theorem OK_isDedekindDomain_and_projective :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), IsDedekindDomain (OK H) ∧ (∀ a : OK H, ∃! m : ℤ × ℤ, a = (m.1 : OK H) + (m.2 : OK H) * wK H) ∧ (∃ br : OK H ≃+* OK H, (∀ a, ((br a : OK H) : 𝓞 E) = H.bar a) ∧ wK H + br (wK H) = 1 ∧ ∀ a, br (br a) = a) ∧ wK H ^ 2 + (((1 + H.d) / 4 : ℕ) : OK H) = wK H ∧ 2 * Module.finrank (OK H) (𝓞 E) = Module.finrank ℚ E ∧
  ∀ (M : Type) [AddCommGroup M] [Module (𝓞 E) M], Module.Finite (𝓞 E) M → Module.Projective (𝓞 E) M → Module.Finite (OK H) M ∧ Module.Projective (OK H) M ∧ Module.finrank (OK H) M = Module.finrank ℚ E / 2 * Module.finrank (𝓞 E) M := by
  intro E _ _ _ H
  have h2 : 2 * Module.finrank (OK H) (𝓞 E) = Module.finrank ℚ E := by
    simpa using two_mul_finrank_OK H (𝓞 E)
  refine ⟨isDedekindDomain_OK H, existsUnique_coord H,
    ⟨barOK H, fun _ => rfl, Subtype.ext ?_, fun a => Subtype.ext (bar_bar H a)⟩, Subtype.ext (cm_generator_sq_quadratic_eq H), h2, ?_⟩
  · change H.w0 + H.bar H.w0 = 1
    rw [cmHost_bar_halfIntegerGenerator, add_sub_cancel]
  · intro M _ _ _ _
    have := finite_int_OK H
    have := isDedekindDomain_OK H
    have : Module.Finite ℤ M := Module.Finite.trans (𝓞 E) M
    have : Module.IsTorsionFree ℤ M := Module.IsTorsionFree.trans (𝓞 E)
    refine ⟨Module.Finite.of_restrictScalars_finite ℤ _ _, Forms.projective_of_int _ _, ?_⟩
    have h3 := two_mul_finrank_OK H M
    rw [← h2, mul_assoc] at h3
    rw [← h2, Nat.mul_div_cancel_left _ two_pos]
    omega

end GlobalTheory.CM
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.RosLam

theorem form_rosati {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (f g : G ⟶ G)
    {V : Type} [CommGroup V] (k : ((G ⊗ G).left ⟶ G.left) → V) :
    (∏ I : ULift.{0} (Finset (Fin 2)),
        k (psum G ![fst G G ≫ f, snd G G] I.down).left ^ ((-1 : ℤ) ^ (2 - I.down.card))) /
      (∏ I : ULift.{0} (Finset (Fin 2)),
        k (psum G ![fst G G, snd G G ≫ g] I.down).left ^ ((-1 : ℤ) ^ (2 - I.down.card))) =
      ∏ i, k (Out.rosatiφ G f g i) ^ Out.rosatiε i := by
  have p := prod_ros f g (fst G G) (snd G G) k
  rw [lift_fst_snd] at p
  simp only [Over.id_left, Category.id_comp] at p
  rw [p, GlobalTheory.NormRos.prod_square, GlobalTheory.NormRos.prod_square]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_div]
  abel

theorem lbIso_of_gen {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left} (hL : L.IsLB)
    (f g : G ⟶ G) (t : LB.Gen (LB.LinComb L (Out.rosatiφ G f g) Out.rosatiε)) (ht : t.IsGen) :
    LBIso (cubeLB G ![fst G G ≫ f, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ g] L) := by
  obtain ⟨Pic, _, cl, pl, h₁, h₂, -, -, h₅, -⟩ := GlobalTheory.CechPicMul.exists_picardGroup
  obtain ⟨a, a'⟩ := h₅ _ _ L hL _ (Out.rosatiφ G f g) Out.rosatiε
  obtain ⟨b, b'⟩ : (cubeLB G ![fst G G ≫ f, snd G G] L).IsLB ∧ cl (cubeLB G ![fst G G ≫ f, snd G G] L) = _ :=
    h₅ _ _ L hL _ _ _
  obtain ⟨c, c'⟩ : (cubeLB G ![fst G G, snd G G ≫ g] L).IsLB ∧ cl (cubeLB G ![fst G G, snd G G ≫ g] L) = _ :=
    h₅ _ _ L hL _ _ _
  refine (h₁ _ _ _ b c).1 ?_
  have e := ((h₂ _ _ a).2 ⟨t, ht⟩).symm.trans a'
  rw [b', c', ← div_eq_one, e]
  have key := form_rosati f g (V := Multiplicative (FreeAddCommGroup ((G ⊗ G).left ⟶ G.left)))
    (fun ψ => Multiplicative.ofAdd (FreeAddCommGroup.of ψ))
  have k := congrArg (AddMonoidHom.toMultiplicativeLeft
    (FreeAddCommGroup.lift fun ψ : (G ⊗ G).left ⟶ G.left => Additive.ofMul (pl ψ (cl L)))) key
  simpa only [map_div, map_prod, map_zpow, AddMonoidHom.coe_toMultiplicativeLeft, Function.comp_apply, toAdd_ofAdd,
    FreeAddCommGroup.lift_apply_of, toMul_ofMul] using k

theorem rosatiAdj_iff_lamEq : Out.GlobalFnsSt → ∀ (S : Scheme.{0}) (P : Out.PolAV S) (f g : P.A ⟶ P.A), IsMonHom f → IsMonHom g → (Out.RosatiAdj P.A P.L f g ↔ LamEq P.L f (𝟙 P.A) P.L (𝟙 P.A) g) := by
  intro hG S P f g hf hg
  have := P.isAb.comm
  unfold LamEq
  rw [Category.comp_id, Category.comp_id]
  constructor
  · intro h
    obtain ⟨u, hu, -⟩ := exists_ros hG P.isAb P.isLB f g h
    exact lbIso_of_gen P.isLB f g u hu
  · intro h s
    obtain ⟨t, ht⟩ := GlobalTheory.NormRos.exists_gen_rosati P.isLB f g h
    exact ⟨⊤, trivial, LB.pullGen P.L _ _ t _, DVR.pullGen_isGen _ _ _ _ ht _⟩

end GlobalTheory.RosLam
end

section

open NumberField IsDedekindDomain MeasureTheory IsLocalRing Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM
open scoped nonZeroDivisors ComplexOrder

theorem _root_.GlobalTheory.T.thetaLine_dual_degree_of_keyFormulaPowerForm : GlobalTheory.KeyFormulaPow → ∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K) (T abelian₂ : MLine K), T.Good → abelian₂.Good → (∀ p, KeyLocAt x T abelian₂ p) → (∀ σ, KeyArchAt x T abelian₂ σ) → T.dual.deg = (1 / 2) * abelian₂.dual.deg + (x.P.g : ℝ) / 4 * (Module.finrank ℚ K : ℝ) * Real.log (2 * Real.pi) := by
  first | exact @GlobalTheory.thetaLine_dual_deg_of_keyFormulaPow | exact GlobalTheory.thetaLine_dual_deg_of_keyFormulaPow | (intros; apply GlobalTheory.thetaLine_dual_deg_of_keyFormulaPow <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF


theorem _root_.GlobalTheory.T.keyLocAt_of_isLocalModel' : ∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K) (T abelian₂ : MLine K) (p : HeightOneSpectrum (𝓞 K)) (a : K) (M : Matrix (Fin x.P.g) (Fin x.P.g) K), KeyPow.IsLocalModel x p a M → IsLocGen p a T.I → IsLocGen p M.det abelian₂.I → KeyLocAt x T abelian₂ p := by
  first | exact @GlobalTheory.LamF.keyLocAt_of_isLocalModel | exact GlobalTheory.LamF.keyLocAt_of_isLocalModel | (intros; apply GlobalTheory.LamF.keyLocAt_of_isLocalModel <;> assumption)
end
