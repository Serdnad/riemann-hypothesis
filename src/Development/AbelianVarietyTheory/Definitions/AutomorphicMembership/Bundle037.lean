module

public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle210
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SimilitudesCorrespond
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle029
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle052
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.RelativeGroupHatForm (IsOver PullsBack lowerCoeff levelMapF endF relGroup trivAt)

namespace GlobalTheory.ShFam.Pad

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l l₂ : Level H}

def CxPt (Xo : Moduli Dw l) (c : Coeff l) : Type :=
  {y : Sp ℂ ⟶ Xo.XF c // y ≫ pullback.snd _ _ = spMap c.F.val.toRingHom}

def LiesOver (h : l.Dvd l₂) {Xo : Moduli Dw l} {c : Coeff l} {Xo₂ : Moduli Dw l₂} {c₂ : Coeff l₂}
    (y₂ : CxPt Xo₂ c₂) (y : CxPt Xo c) : Prop :=
  ∃ π : Xo₂.X ⟶ Xo.X, IsOver h Xo Xo₂ π ∧ PullsBack Xo Xo₂ π ∧
    y₂.1 ≫ pullback.fst _ _ ≫ π = y.1 ≫ pullback.fst _ _


open Classical in
def levDeg (h : l.Dvd l₂) (Xo : Moduli Dw l) (c : Coeff l) (Xo₂ : Moduli Dw l₂) (c₂ : Coeff l₂) : ℕ :=
  if k : ∃ n, 0 < n ∧ ∀ y : CxPt Xo c, Nat.card {y₂ : CxPt Xo₂ c₂ // LiesOver h y₂ y} = n then Nat.find k else 1

theorem levDeg_pos (h : l.Dvd l₂) (Xo : Moduli Dw l) (c : Coeff l) (Xo₂ : Moduli Dw l₂) (c₂ : Coeff l₂) :
    0 < levDeg h Xo c Xo₂ c₂ := by
  classical
  unfold levDeg
  split_ifs with k
  · exact (Nat.find_spec k).1
  · exact one_pos

theorem card_lifts_pos {k : Type} [Field k] [IsAlgClosed k] {X Y : Scheme.{0}} (π : X ⟶ Y) [IsFinite π] [Surjective π]
    (y : Sp k ⟶ Y) : 0 < Nat.card {x : Sp k ⟶ X // x ≫ π = y} := by
  have hne : Nonempty {x : Sp k ⟶ X // x ≫ π = y} := by
    have : CompactSpace ↥(pullback π y) := QuasiCompact.compactSpace_of_compactSpace (pullback.snd π y)
    obtain ⟨p, -⟩ := (pullback.snd π y).surjective (default : PrimeSpectrum k)
    obtain ⟨q, -, hq⟩ := isClosed_univ.exists_closed_singleton (X := ↥(pullback π y)) ⟨p, trivial⟩
    refine ⟨pointOfClosedPoint (pullback.snd π y) q hq ≫ pullback.fst π y, ?_⟩
    rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp, Category.id_comp]
  have hfin : Finite {x : Sp k ⟶ X // x ≫ π = y} := by
    have hf := (pullback.snd π y).finite_preimage_singleton (IsLocalRing.closedPoint k)
    have := hf.to_subtype
    let s : {x : Sp k ⟶ X // x ≫ π = y} → (Sp k ⟶ pullback π y) := fun x =>
      pullback.lift x.1 (𝟙 _) (x.2.trans (Category.id_comp _).symm)
    refine Finite.of_injective (β := (pullback.snd π y) ⁻¹' {IsLocalRing.closedPoint k})
      (fun x => ⟨s x (IsLocalRing.closedPoint k), Subsingleton.elim (α := PrimeSpectrum k) _ _⟩) fun a b e => ?_
    have e' : s a = s b := ext_of_apply_closedPoint_eq (pullback.snd π y) (pullback.lift_snd _ _ _)
      (pullback.lift_snd _ _ _) (congrArg Subtype.val e)
    exact Subtype.ext ((pullback.lift_fst _ _ _).symm.trans ((congrArg (· ≫ pullback.fst π y) e').trans
      (pullback.lift_fst _ _ _)))
  exact Nat.card_pos

theorem card_liesOver_eq_index (hpq : 1 ≤ Dw.p + Dw.q) (h : l.Dvd l₂) {Xo : Moduli Dw l} {c : Coeff l}
    (Xo₂ : Moduli Dw l₂) (c₂ : Coeff l₂) (y : CxPt Xo c) :
    0 < Nat.card {y₂ : CxPt Xo₂ c₂ // LiesOver h y₂ y} ∧
      Nat.card {y₂ : CxPt Xo₂ c₂ // LiesOver h y₂ y} = ((trivAt Dw l₂).subgroupOf (relGroup Dw l l₂)).index := by
  obtain ⟨π, hπ, hpb, huniq, ρ, hρ, hone, hmul, -, hρπ, hcov⟩ :=
    (GlobalTheory.LevelCompare.levelMaps_iff hpq).1 (GlobalTheory.moduliScheme_levelMaps_heckePoints.2 E H Dw hpq).1 l l₂ h Xo Xo₂
  obtain ⟨k₁, -, k₃, k₄⟩ := hcov c₂
  have w : (y.1 ≫ pullback.fst _ _) ≫ Xo.s =
      spMap c₂.F.val.toRingHom ≫ spMap (IntermediateField.inclusion (lowerCoeff h c₂).le).toRingHom := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, y.2, ← Spec.map_comp, ← Spec.map_comp]
    rfl
  let y' : Sp ℂ ⟶ Xo.XF (lowerCoeff h c₂) := pullback.lift _ _ w
  have hf : levelMapF h hπ c₂ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ π := pullback.lift_fst _ _ _
  have hs := GlobalTheory.LevelCompare.levelMapF_snd h hπ c₂
  let e : {y₂ : CxPt Xo₂ c₂ // LiesOver h y₂ y} ≃ {x : Sp ℂ ⟶ Xo₂.XF c₂ // x ≫ levelMapF h hπ c₂ = y'} :=
    { toFun := fun a => ⟨a.1.1, by
        obtain ⟨π', a₁, a₂, a₃⟩ := a.2
        obtain rfl := huniq π' a₁ a₂
        refine pullback.hom_ext ?_ ?_
        · rw [Category.assoc, hf, a₃]; exact (pullback.lift_fst _ _ _).symm
        · rw [Category.assoc, hs]; exact a.1.2.trans (pullback.lift_snd _ _ _).symm⟩
      invFun := fun x => ⟨⟨x.1, (congrArg (x.1 ≫ ·) hs.symm).trans ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ pullback.snd _ _) x.2).trans (pullback.lift_snd _ _ _)))⟩, π, hπ, hpb, by
        change x.1 ≫ _ = _
        rw [← hf, ← Category.assoc, x.2]; exact pullback.lift_fst _ _ _⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hpos := card_lifts_pos (levelMapF h hπ c₂) y'
  rw [Nat.card_congr e]
  refine ⟨hpos, ?_⟩
  obtain ⟨⟨x, hx⟩⟩ := (Nat.card_pos_iff.1 hpos).1
  have hF : ∀ g, endF (ρ g).hom (hρ g) c₂ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ (ρ g).hom := fun g =>
    pullback.lift_fst _ _ _
  have hS : ∀ g, endF (ρ g).hom (hρ g) c₂ ≫ pullback.snd _ _ = pullback.snd _ _ := fun g => pullback.lift_snd _ _ _
  have hm : ∀ g g', endF (ρ (g * g')).hom (hρ _) c₂ = endF (ρ g).hom (hρ g) c₂ ≫ endF (ρ g').hom (hρ g') c₂ :=
    fun g g' => pullback.hom_ext (by rw [hF, Category.assoc, hF, ← Category.assoc, hF, hmul, Category.assoc]; rfl)
      (by rw [hS, Category.assoc, hS, hS])
  have h1 : endF (ρ 1).hom (hρ _) c₂ = 𝟙 _ :=
    pullback.hom_ext (by rw [hF, hone, Category.id_comp]; exact Category.comp_id _) (by rw [hS, Category.id_comp])
  let f : relGroup Dw l l₂ → {x : Sp ℂ ⟶ Xo₂.XF c₂ // x ≫ levelMapF h hπ c₂ = y'} := fun g =>
    ⟨x ≫ endF (ρ g).hom (hρ g) c₂, by
      rw [← hx, Category.assoc]
      congr 1
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, hf, ← Category.assoc, hF, Category.assoc, hρπ]
      · rw [Category.assoc, hs]; exact hS g⟩
  have hsurj : Function.Surjective f := fun a => by
    obtain ⟨g, hg⟩ := (k₄ ℂ x).1 a.1 (a.2.trans hx.symm)
    exact ⟨g, Subtype.ext hg⟩
  have hker : Setoid.ker f = QuotientGroup.rightRel ((trivAt Dw l₂).subgroupOf (relGroup Dw l l₂)) := by
    ext g g'
    rw [QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf, ← (k₄ ℂ x).2, Setoid.ker_def, Subtype.ext_iff, hm]
    change x ≫ _ = x ≫ _ ↔ _
    constructor
    · intro a
      rw [← Category.assoc, ← a, Category.assoc, ← hm, mul_inv_cancel, h1, Category.comp_id]
    · intro a
      have := congrArg (· ≫ endF (ρ g).hom (hρ g) c₂) a
      simp only [Category.assoc] at this
      rw [← hm, inv_mul_cancel, h1, Category.comp_id] at this
      exact this.symm
  rw [← Nat.card_congr (Setoid.quotientKerEquivOfSurjective f hsurj), hker,
    Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel _)]
  rfl

theorem card_liesOver (hpq : 1 ≤ Dw.p + Dw.q) (h : l.Dvd l₂) {Xo : Moduli Dw l} {c : Coeff l}
    (Xo₂ : Moduli Dw l₂) (c₂ : Coeff l₂) (y : CxPt Xo c) :
    Nat.card {y₂ : CxPt Xo₂ c₂ // LiesOver h y₂ y} = levDeg h Xo c Xo₂ c₂ := by
  classical
  have k : ∃ n, 0 < n ∧ ∀ y : CxPt Xo c, Nat.card {y₂ : CxPt Xo₂ c₂ // LiesOver h y₂ y} = n :=
    ⟨_, (card_liesOver_eq_index hpq h Xo₂ c₂ y).1, fun y' =>
      (card_liesOver_eq_index hpq h Xo₂ c₂ y').2.trans (card_liesOver_eq_index hpq h Xo₂ c₂ y).2.symm⟩
  rw [levDeg, dite_eq_left k]
  exact (Nat.find_spec k).2 y

end GlobalTheory.ShFam.Pad
end
end

section

noncomputable section

namespace GlobalTheory.HeightCounting.Up.RowModel

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting
  GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings

attribute [local instance] Formalism.BasicNotions.Host.cmStar




theorem overRows_allSt {p : RowP} (h : OverRows p) :
    AllSt fun K B f T w P x => p K B f T w x.o.Z P.Wt P.hX x.m.z x.s.p0 x.r.Y :=
  EvG.imp h fun _ _ _ _ _ hK => large₂.imp hK fun _ _ _ _ H kp _ _ w s P x =>
    s.1.elim fun c => H kp w c x.o.Z P.Wt P.hX x.m.z x.s.p0 x.r.Y x.m.intersectionNumber_baseChange x.m.exAt x.m.inGeo x.fits.grp x.fits.grpAt


end GlobalTheory.HeightCounting.Up.RowModel

end
end

section

noncomputable section

namespace GlobalTheory.HeightCounting.Up.Model

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting
  GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar




variable {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}

theorem qOf_off (v : B.places.Pl) (h : v ∉ P.Wt) : QOf P v = ∅ := if_neg h

theorem qOf_on (v : B.places.Pl) (h : v ∈ P.Wt) : QOf P v = T.Q v := if_pos h

theorem qOf_eq (v : B.places.Pl) : QOf P v = T.Q v := by
  by_cases h : v ∈ P.Wt
  · exact qOf_on v h
  · rw [qOf_off v h]
    refine (Finset.eq_empty_of_forall_notMem fun u hu => ?_).symm
    have h1 := ((T.psi_is v).ram u).1 (by rw [P.supp v h]; exact fun _ _ => rfl)
    exact h1 hu

theorem mem_of_twisted (x : St P) (v : B.places.Pl) (h : TwistedAt (Dof x) v) : v ∈ P.Wt := by
  by_contra hv
  exact h (P.q.mu.off v hv)

theorem del_mul_ne_one {p : ℕ} (hp : p.Prime) (hS : p ∈ offSet B.toPre) {δ : HChar B.host.E} (hδ : IsDelta (H := B.host) p δ)
    (v : B.places.Pl) : δ * T.psi v ≠ 1 := by
  intro h
  obtain ⟨Q, hQ, hpQ⟩ : ∃ Q : Ideal (𝓞 B.host.E), Q.IsMaximal ∧ ((p : ℕ) : 𝓞 B.host.E) ∈ Q := by
    have hne : Ideal.span {((p : ℕ) : 𝓞 B.host.E)} ≠ ⊤ := by
      intro ht
      have := congrArg Ideal.absNorm ht
      rw [Ideal.absNorm_span_singleton, Ideal.absNorm_top] at this
      have h2 : Algebra.norm ℤ ((p : ℕ) : 𝓞 B.host.E) = (p : ℤ) ^ Module.finrank ℤ (𝓞 B.host.E) := by
        rw [← map_natCast (algebraMap ℤ (𝓞 B.host.E)), Algebra.norm_algebraMap]
      rw [h2, Int.natAbs_pow, Int.natAbs_natCast] at this
      rcases Nat.pow_eq_one.1 this with h3 | h3
      · exact hp.one_lt.ne' h3
      · exact Module.finrank_pos.ne' h3
    obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal _ hne
    exact ⟨Q, hQ, hle (Ideal.subset_span rfl)⟩
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    exact hp.ne_zero (by exact_mod_cast (Ideal.mem_bot.1 hpQ))
  let u : HeightOneSpectrum (𝓞 B.host.E) := ⟨Q, hQ.isPrime, hQ0⟩
  have hu : OverP B.host p u := hpQ
  have hψ : (T.psi v).UnrAt u := by
    by_contra hn
    obtain ⟨-, h1, -, h2⟩ := (T.psi_tw v).2.2.2 u hn
    have h3 : ((Ideal.absNorm u.asIdeal : ℕ) : 𝓞 B.host.E) ∈ u.asIdeal := Ideal.absNorm_mem _
    by_cases e : Ideal.absNorm u.asIdeal = p
    · exact h2 (e ▸ hS)
    · obtain ⟨a, b, hab⟩ : IsCoprime ((Ideal.absNorm u.asIdeal : ℕ) : 𝓞 B.host.E) (p : 𝓞 B.host.E) :=
        Nat.Coprime.cast ((Nat.coprime_primes h1 hp).2 e)
      exact u.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hab ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ h3) (Ideal.mul_mem_left _ _ hpQ)))
  have h15 := (hδ.ine u hu 1).1 fun x hx => by
    have e := congrArg (fun χ : HChar B.host.E => χ.loc u x) h
    change δ.loc u x * (T.psi v).loc u x = 1 at e
    rw [hψ x hx, mul_one] at e
    rw [pow_one, e]
  omega

theorem twisted_iff (x : St P) (v : B.places.Pl) : TwistedAt (Dof x) v ↔ v ∈ P.Wt := by
  refine ⟨mem_of_twisted x v, fun hv h => ?_⟩
  have h1 : P.q.W₀.muTw v = w.C.mu0 := (P.q.mu.on v hv).symm.trans h
  have h2 := P.q.mu.tw v
  rw [h1] at h2
  have h3 : T.xiTw f v = 1 := h2.symm.trans w.ok.trueColumnChoices_heckeChar_reference_eq_one
  unfold TwDat.xiTw at h3
  split_ifs at h3
  · exact del_mul_ne_one B.host.pde'_prime (by simp [offSet]) f.isDel' v h3
  · exact del_mul_ne_one B.host.pde_prime (by simp [offSet]) f.isDel v h3

end GlobalTheory.HeightCounting.Up.Model

end
end

section

noncomputable section

namespace GlobalTheory.HeightCounting.Up.ListModel

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 Formalism.L2.Host Formalism.IndefR.Links NumberField IsDedekindDomain GlobalTheory.ChiGrid GlobalTheory.BigTop.Fun

attribute [local instance] Formalism.BasicNotions.Host.cmStar




section Guard

open Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR GlobalTheory.BigTop

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

end Guard

variable (hL : GlobalTheory.Published.LocalLanglandsGL) (cDep : ℝ)






open GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3.Rw in
theorem lev_at_state {K : Ctx} {B : GlobalTheory.Mem.Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) :
    x.m.z.R.toRealDat.toLevCh.C = cfOf x ∧ ∃ μ0, x.m.z.R.toRealDat.toLevCh.Is μ0 :=
  by
    constructor
    · exact x.m.z.lev.C
    · exact ⟨_, x.m.z.lev.is⟩


open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 in
theorem nonempty_grid {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (Z : w.Lt) {hX : B.fields.Ok} {Wt : Set B.places.Pl}
    (z : Dat (w.st Z) w.I hX T Wt) (sc : Consts) (h3 : ∀ k, q0 (w.st Z).toD7 ≠ B.host.g k) :
    Nonempty (GridData z.R.toRealDat.toLevCh sc) := by
  refine GlobalTheory.ChiGridModel.nonempty_gridData _ _ z.lev.is sc B.g_cond B.pde_cond.1 B.pde_cond.2 h3 fun t PP hP hq => ?_
  have hprime := (GlobalTheory.ChiGrid.leastSplitAuxiliaryPrimeThetaChain_spec (w.st Z).toD7).1
  have two : ∀ p : ℕ, p.Prime → ((p : ℕ) : 𝓞 B.host.E) ∈ PP.asIdeal → q0 (w.st Z).toD7 = p := fun p hp hm => by
    by_contra hne
    have hc : IsCoprime ((q0 (w.st Z).toD7 : ℕ) : 𝓞 B.host.E) ((p : ℕ) : 𝓞 B.host.E) :=
      Nat.Coprime.cast ((Nat.coprime_primes hprime hp).2 hne)
    obtain ⟨a, b, hab⟩ := hc
    exact PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hab ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ hq) (Ideal.mul_mem_left _ _ hm)))
  have hd : f.del.UnrAt PP := f.isDel.unr PP fun h => (GlobalTheory.ChiGrid.leastSplitAuxiliaryPrime_ne_typePrimes (w.st Z).toD7).1 (two _ B.host.pde_prime h)
  have hd' : f.del'.UnrAt PP := f.isDel'.unr PP fun h => (GlobalTheory.ChiGrid.leastSplitAuxiliaryPrime_ne_typePrimes (w.st Z).toD7).2 (two _ B.host.pde'_prime h)
  have hps : ∀ v, (T.psi v).UnrAt PP := fun v => by
    by_contra hn
    obtain ⟨-, h1, -, h2⟩ := (T.psi_tw v).2.2.2 PP hn
    have hmem := Ideal.absNorm_mem PP.asIdeal
    have e := two _ h1 hmem
    exact h2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e.symm))))))
  refine (z.lev.is.Q_ram t PP).2 (Or.inl hP) ?_
  rw [z.lev.xiH t]
  have hm : w.I.xi (GlobalTheory.Mem.R3.ixOf w.I _ t) ∈ T.set f := w.xi_range ▸ ⟨_, rfl⟩
  rcases hm with (h | h | h) | ⟨v, h⟩
  · rw [h]; intro x _; rfl
  · exact h ▸ hd
  · exact (h : _ = _) ▸ hd'
  · rw [← h]
    unfold TwDat.xiTw
    split_ifs
    · exact HChar.UnrAt.mul hd' (hps v)
    · exact HChar.UnrAt.mul hd (hps v)

end GlobalTheory.HeightCounting.Up.ListModel

end
end
