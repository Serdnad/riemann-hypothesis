module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.IsFirstChernClassInFamily
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.Bundle001
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.FaceMapCompSuccAboveCastSucc
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.EtDefs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ChainOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle246
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle275
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle267
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle229
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle230
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle244
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle268
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle248
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatFinal
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
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris Formalism.Per6

universe w w' v u v' u'

namespace CrystallineSemistableComparison.HT.Red

open CH PAlg B

section Gen
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
  {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w'} R}

theorem sub_mulSub (m : CH.Mor F F' (RingHom.id R)) (c : R) (S₁ S₂ : SubF F) (S₁' S₂' : SubF F') (h₁ h₂ k k') (j : ℕ) (x : H S₁.fn j) :
    (subMor m S₂ S₂' h₂).pull j ((mulSub c S₁ S₂ k).pull j x) = (mulSub c S₁' S₂' k').pull j ((subMor m S₁ S₁' h₁).pull j x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => Subtype.ext (map_smul (m.τ _) c _)))

theorem sub_mulTo (m : CH.Mor F F' (RingHom.id R)) (c : R) (S : SubF F) (S' : SubF F') (h k k') (j : ℕ) (x : H F j) :
    (subMor m S S' h).pull j ((mulTo c S k).pull j x) = (mulTo c S' k').pull j (m.pull j x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => Subtype.ext (map_smul (m.τ _) c _)))

theorem mulSub_mulTo (c c' c'' : R) (e : c'' = c' * c) (S S' : SubF F) (k k' k'') (j : ℕ) (x : H F j) :
    (mulSub c' S S' k').pull j ((mulTo c S k).pull j x) = (mulTo c'' S' k'').pull j x := by
  subst e
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => Subtype.ext (mul_smul c' c _).symm))

end Gen

section Pd
variable {b b' : Base} {L : b.Fun} {L' : b'.Fun} {Λ : Type} [CommRing Λ] {c : Λ →+* b.R} {c' : Λ →+* b'.R} {σ : b.R →+* b'.R}

theorem om_sh (m : GlobalTheory.LogCris.Mor L L' σ) (h : ∀ a, σ (c a) = c' (RingHom.id Λ a)) {t : Λ} (ht : c t ∈ b.I) (ht' : c' t ∈ b'.I)
    {r r' : ℕ} (k : ℕ) (e : r + k = r') (j : ℕ) (x : H (pdS L c r).fn j) :
    (pdOm m (RingHom.id Λ) h r').pull j ((pdSh L c ht k e).pull j x) =
      (pdSh L' c' ht' k e).pull j ((pdOm m (RingHom.id Λ) h r).pull j x) :=
  sub_mulSub (omMor m (RingHom.id Λ) h) (t ^ k) _ _ _ _ _ _ _ _ j x

end Pd

section PdCr
variable {O : Type} [CommRing O] {F : Fn O} {b : Base} {ht : b.t = 1} {κ : O →+* b.R ⧸ b.I}

theorem cr_pull_eq' {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] {c : Λ →+* b.R} {σ : Λ →+* Λ'} {C' : Type u} [Category.{v} C']
    {F' : C' ⥤ ModuleCat.{w} Λ'} (r : ℕ) (m m' : CH.Mor (pdS (F.cr b ht κ) c r).fn F' σ) (η : ∀ T, m.G.obj T ⟶ m'.G.obj T)
    (nat : ∀ {T T' : C'} (f : T ⟶ T') (x : (m.G.obj T).B), (η T').φ ((m.G.map f).φ x) = (m'.G.map f).φ ((η T).φ x))
    (hτ : ∀ (T : C') x, m'.τ T (((pdS (F.cr b ht κ) c r).fn.map (η T)).hom x) = m.τ T x) (n : ℕ) (x : H (pdS (F.cr b ht κ) c r).fn n) :
    m.pull n x = m'.pull n x :=
  CrystallineSemistableComparison.P.prism m m' ⟨η, fun _ _ f => Thick.Hom.ext (RingHom.ext (nat f)) (funext fun j => j.elim)⟩ hτ n x

end PdCr

theorem map_eq (P : CommRingCat.{0} ⥤ Type) {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B)
    (g : B →+* C) (h : A →+* C) (e : g.comp f = h) (y : P.obj (CommRingCat.of A)) :
    P.map (CommRingCat.ofHom g) (P.map (CommRingCat.ofHom f) y) = P.map (CommRingCat.ofHom h) y := by
  rw [← Functor.map_comp_apply, ← CommRingCat.ofHom_comp, e]

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l)

def redT (P : PAlg l ⥤ Type) (r n : ℕ) : CH.Mor (TT P r (n + 1)).fn (TT P r n).fn (RingHom.id _) :=
  subMor (CH.Mor.ofNatTrans (redEl P n.le_succ)) _ _ fun T x hx =>
    mem_TT.2 (Pb.dividedPowerFiltration_map (dd_red false T.1.obj n.le_succ) r (mem_TT.1 hx))

theorem reduction_commutes_tMor (ht : TFil l) (P : PAlg l ⥤ Type) (r n j : ℕ) (y : MH P (n + 1) j) :
    (redT P r n).pull j ((tMor ht P r (n + 1)).pull j y) = (tMor ht P r n).pull j ((MSys P j).r n y) :=
  sub_mulTo (CH.Mor.ofNatTrans (redEl P n.le_succ)) (tA l ^ r) _ _ _ _ _ j y

theorem red_uJ (k : Bool) (A : PAlg l) {m n : ℕ} (h : n ≤ m) (hle : JJ k A m ≤ (JJ k A n).comap (A.red h)) :
    (Ideal.quotientMap _ (A.red h) hle).comp (uJ k A m) = uJ k A n :=
  Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)

theorem red_comm (A : PAlg l) {m n : ℕ} (h : n ≤ m) (r : (base l).Acr m) :
    A.red h (mapAcr A.fromBase m r) = mapAcr A.fromBase n ((base l).red h r) :=
  PdOk.red_acr (pdOk_hom A.fromBase) h r

def redTh (n : ℕ) (T : El (F.pt κ)) :
    (gT F κ false (n + 1)).obj T ⟶ (SH.redM F κ false n).functor.obj ((gT F κ false n).obj T) :=
  crHom (T := gObj F κ false (n + 1) ((jE _).obj T)) (T' := (SH.redM F κ false n).obj (gObj F κ false n ((jE _).obj T)))
    (T.1.obj.red n.le_succ) (red_comm T.1.obj n.le_succ) (dd_red false T.1.obj n.le_succ)
    fun h => map_eq F.Pt _ _ _ (red_uJ false T.1.obj n.le_succ h) T.2.1

theorem β_red (r n j : ℕ) (x : H (pdS (Lc F κ false (n + 1)) ((base l).cris (n + 1)) r).fn j) :
    (βMorF F κ r n).pull j ((pdOm (SH.redM F κ false n) (RingHom.id _) (red_cris _ n.le_succ) r).pull j x) =
      (redT (F.pt κ) r n).pull j ((βMorF F κ r (n + 1)).pull j x) :=
  ((pull_pull (RingHom.id _) (pdOm (SH.redM F κ false n) (RingHom.id _) (red_cris _ n.le_succ) r) (βMorF F κ r n) j x).trans
    (cr_pull_eq' r ((βMorF F κ r (n + 1)).comp (redT (F.pt κ) r n))
      ((pdOm (SH.redM F κ false n) (RingHom.id _) (red_cris _ n.le_succ) r).comp (βMorF F κ r n)) (redTh F κ n)
      (fun f x => PdOk.red_acr (pdOk_hom f.1.hom) n.le_succ x) (fun T x => rfl) j x).symm).trans
    (pull_pull (RingHom.id _) (βMorF F κ r (n + 1)) (redT (F.pt κ) r n) j x).symm

theorem tt_mul (ht : TFil l) (P : PAlg l ⥤ Type) {r r' : ℕ} (k : ℕ) (e : r + k = r') (n : ℕ) (T : El P)
    (x : (modF (AcrEl P n)).obj T) (hx : x ∈ (TT P r n).S T) : tA l ^ k • x ∈ (TT P r' n).S T := by
  have := dividedPowerFiltration_pow_mul (DD false T.1.obj n) (ht T.1.obj n) e (mem_TT.1 hx)
  rw [← map_pow] at this
  exact mem_TT.2 this

theorem β_sh (ht : TFil l) {r r' : ℕ} (k : ℕ) (e : r + k = r') (n j : ℕ) (x : H (pdS (Lc F κ false n) ((base l).cris n) r).fn j)
    (y : MH (F.pt κ) n j) (h : (βMorF F κ r n).pull j x = (tMor ht (F.pt κ) r n).pull j y) :
    (βMorF F κ r' n).pull j ((pdSh (Lc F κ false n) ((base l).cris n) (ht (base l) n) k e).pull j x) =
      (tMor ht (F.pt κ) r' n).pull j y :=
  (sub_mulSub (βMor F κ false n) (tA l ^ k) _ _ _ _ _ _ _ (tt_mul ht (F.pt κ) k e n) j x).trans
    ((congrArg ((mulSub (tA l ^ k) (TT (F.pt κ) r n) (TT (F.pt κ) r' n) (tt_mul ht (F.pt κ) k e n)).pull j) h).trans
      (mulSub_mulTo (tA l ^ r) (tA l ^ k) (tA l ^ r') (by rw [← e, add_comm, pow_add]) _ _ _ _ _ j y))

end CrystallineSemistableComparison.HT.Red
end
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers GroundTheory.PAdicHodge Formalism.Per6

namespace CrystallineSemistableComparison.HT

open CH PAlg

section Gen
variable {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {C C' : Type 1} [Category.{0} C] [Category.{0} C']

theorem subMor_cup {A : C ⥤ CommAlgCat.{0} R} {A' : C' ⥤ CommAlgCat.{0} R'} (m : CH.Mor (modF A) (modF A') σ)
    (hm : ∀ (T : C') (x y : A.obj (m.G.obj T)), m.τ T (x * y) = (show A'.obj T from m.τ T x) * (show A'.obj T from m.τ T y))
    {S₁ S₂ S₃ : SubF (modF A)} {S₁' S₂' S₃' : SubF (modF A')} (h₁ h₂ h₃) (hS hS') {p q n : ℕ} (h : p + q = n)
    (x : H S₁.fn p) (y : H S₂.fn q) :
    (subMor m S₃ S₃' h₃).pull n ((subPair S₁ S₂ S₃ hS).cup h x y) =
      (subPair S₁' S₂' S₃' hS').cup h ((subMor m S₁ S₁' h₁).pull p x) ((subMor m S₂ S₂' h₂).pull q y) :=
  CrystallineSemistableComparison.P.cup_pull (subPair S₁ S₂ S₃ hS) (subPair S₁' S₂' S₃' hS') m.G (subMor m S₁ S₁' h₁).τ (subMor m S₂ S₂' h₂).τ
    (subMor m S₃ S₃' h₃).τ (subMor m S₁ S₁' h₁).nat (subMor m S₂ S₂' h₂).nat (subMor m S₃ S₃' h₃).nat
    (fun T x y => Subtype.ext (hm T _ _)) h x y

theorem mulTo_cup {A : C ⥤ CommAlgCat.{0} R} {c₁ c₂ c₃ : R} (hc : c₃ = c₁ * c₂) {S₁ S₂ S₃ : SubF (modF A)} (h₁ h₂ h₃) (hS)
    {p q n : ℕ} (h : p + q = n) (x : H (modF A) p) (y : H (modF A) q) :
    (mulTo c₃ S₃ h₃).pull n ((mulP A).cup h x y) =
      (subPair S₁ S₂ S₃ hS).cup h ((mulTo c₁ S₁ h₁).pull p x) ((mulTo c₂ S₂ h₂).pull q y) :=
  CrystallineSemistableComparison.P.cup_pull (mulP A) (subPair S₁ S₂ S₃ hS) (𝟭 C) (mulTo c₁ S₁ h₁).τ (mulTo c₂ S₂ h₂).τ
    (mulTo c₃ S₃ h₃).τ (mulTo c₁ S₁ h₁).nat (mulTo c₂ S₂ h₂).nat (mulTo c₃ S₃ h₃).nat
    (fun T (x y : A.obj T) => Subtype.ext (show c₃ • (x * y) = (c₁ • x) * (c₂ • y) by rw [hc, smul_mul_smul_comm])) h x y

theorem subMor_one {A : C ⥤ CommAlgCat.{0} R} {A' : C' ⥤ CommAlgCat.{0} R'} (m : CH.Mor (modF A) (modF A') σ)
    (hm : ∀ T : C', m.τ T (1 : A.obj (m.G.obj T)) = (1 : A'.obj T)) {c : R} {c' : R'} (hc : c = 1) (hc' : c' = 1)
    {S : SubF (modF A)} {S' : SubF (modF A')} (h h₁ h₂) :
    (subMor m S S' h).pull 0 ((mulTo c S h₁).pull 0 (CH.oneH A)) = (mulTo c' S' h₂).pull 0 (CH.oneH A') := by
  subst hc hc'
  refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => Subtype.ext ?_))
  change m.τ _ ((1 : R) • (1 : A.obj _)) = (1 : R') • (1 : A'.obj _)
  rw [one_smul, one_smul, hm]

end Gen

section Pd
variable {b b' : Base} {L : b.Fun} {L' : b'.Fun} {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] {c : Λ →+* b.R} {c' : Λ' →+* b'.R}
  {σ : b.R →+* b'.R} (m : GlobalTheory.LogCris.Mor L L' σ) (σ₀ : Λ →+* Λ') (hσ : ∀ a, σ (c a) = c' (σ₀ a))

theorem pdOm_cup {r r' s : ℕ} (e : r + r' = s) {p q n : ℕ} (h : p + q = n) (x : H (B.pdS L c r).fn p) (y : H (B.pdS L c r').fn q) :
    (pdOm m σ₀ hσ s).pull n ((pdPair L c e).cup h x y) =
      (pdPair L' c' e).cup h ((pdOm m σ₀ hσ r).pull p x) ((pdOm m σ₀ hσ r').pull q y) :=
  subMor_cup (A := B.OA L c) (A' := B.OA L' c') (B.omMor m σ₀ hσ) (fun _ _ _ => rfl) _ _ _ _ _ h x y

theorem pdOm_one : (pdOm m σ₀ hσ 0).pull 0 (pdOne L c) = pdOne L' c' :=
  subMor_one (A := B.OA L c) (A' := B.OA L' c') (B.omMor m σ₀ hσ) (fun _ => rfl) rfl rfl _ _ _

end Pd

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

def ttPair (P : PAlg l ⥤ Type) (n : ℕ) {r r' s : ℕ} (h : r + r' = s) : Pairing (TT P r n).fn (TT P r' n).fn (TT P s n).fn :=
  subPair (A := AcrEl P n) (TT P r n) (TT P r' n) (TT P s n) fun T x y hx hy =>
    mem_TT.2 (h ▸ dividedPowerFiltration_mul (B.DD false T.1.obj n) r r' (mem_TT.1 hx) (mem_TT.1 hy))

section F
variable {O : Type} [CommRing O] (F : B.Fn O) (κ : O →+* OC l)

theorem βF_cup (n : ℕ) {r r' s : ℕ} (e : r + r' = s) {p q k : ℕ} (h : p + q = k)
    (x : H (B.pdS (B.Lc F κ false n) ((base l).cris n) r).fn p) (y : H (B.pdS (B.Lc F κ false n) ((base l).cris n) r').fn q) :
    (βMorF F κ s n).pull k ((pdPair (B.Lc F κ false n) ((base l).cris n) e).cup h x y) =
      (ttPair (F.pt κ) n e).cup h ((βMorF F κ r n).pull p x) ((βMorF F κ r' n).pull q y) :=
  subMor_cup (A := B.OcA F κ false n) (A' := AcrEl (F.pt κ) n) (B.βMor F κ false n) (fun _ _ _ => rfl) _ _ _ _ _ h x y

theorem βF_one (ht : TFil l) (n : ℕ) : (βMorF F κ 0 n).pull 0 (pdOne (B.Lc F κ false n) ((base l).cris n)) =
    (tMor ht (F.pt κ) 0 n).pull 0 (CH.oneH (AcrEl (F.pt κ) n)) :=
  subMor_one (A := B.OcA F κ false n) (A' := AcrEl (F.pt κ) n) (B.βMor F κ false n) (fun _ => rfl) rfl (pow_zero _) _ _ _

end F

theorem tMor_cup (ht : TFil l) (P : PAlg l ⥤ Type) (n : ℕ) {r r' s : ℕ} (e : r + r' = s) {p q k : ℕ} (h : p + q = k)
    (x : MH P n p) (y : MH P n q) :
    (tMor ht P s n).pull k ((mulP (AcrEl P n)).cup h x y) =
      (ttPair P n e).cup h ((tMor ht P r n).pull p x) ((tMor ht P r' n).pull q y) :=
  mulTo_cup (A := AcrEl P n) (by rw [← e, pow_add]) _ _ _ _ h x y

theorem comp_cup {M : Model l K} {r r' s i j : ℕ} (h : r + r' = s) {x : Fam M r i} {y : Fam M r' j} (hx : Comp x) (hy : Comp y) :
    Comp (cupS h x y) := fun n =>
  (pdOm_cup (CrystallineSemistableComparison.SH.redM (B.schFn M.p) (okToOC l K) false n) (RingHom.id _) (B.red_cris _ n.le_succ) h rfl
    (x (n + 1)) (y (n + 1))).trans
    (congrArg₂ ((pdPair (M.L false n) ((base l).cris n) h).cup rfl) (hx n) (hy n))

theorem comp_one (M : Model l K) : Comp (oneS M) := fun n =>
  pdOm_one (CrystallineSemistableComparison.SH.redM (B.schFn M.p) (okToOC l K) false n) (RingHom.id _) (B.red_cris _ n.le_succ)

theorem cup_gen (ht : TFil l) {O : Type} [CommRing O] (F : B.Fn O) (κ : O →+* OC l) (n : ℕ) {r r' s i j : ℕ} (e : r + r' = s)
    (x : H (B.pdS (B.Lc F κ false n) ((base l).cris n) r).fn i) (y : H (B.pdS (B.Lc F κ false n) ((base l).cris n) r').fn j)
    (a : MH (F.pt κ) n i) (b : MH (F.pt κ) n j) (w : MH (F.pt κ) n (i + j))
    (hw : w = (mulP (AcrEl (F.pt κ) n)).cup rfl a b)
    (hx : (βMorF F κ r n).pull i x = (tMor ht (F.pt κ) r n).pull i a)
    (hy : (βMorF F κ r' n).pull j y = (tMor ht (F.pt κ) r' n).pull j b) :
    (βMorF F κ s n).pull (i + j) ((pdPair (B.Lc F κ false n) ((base l).cris n) e).cup rfl x y) =
      (tMor ht (F.pt κ) s n).pull (i + j) w :=
  ((βF_cup F κ n e rfl x y).trans (congrArg₂ ((ttPair (F.pt κ) n e).cup rfl) hx hy)).trans
    ((tMor_cup ht (F.pt κ) n e rfl a b).symm.trans (congrArg ((tMor ht (F.pt κ) s n).pull (i + j)) hw.symm))

variable (ht : TFil l) {e : E.EtFam l K}

theorem isLift_cupS_of_cupT (he : EtP e) : ∀ {M : Model l K} {r r' s i j : ℕ} (h : r + r' = s) {v : M.T i} {v' : M.T j} {w : M.T (i + j)}
    {x : Fam M r i} {x' : Fam M r' j}, M.CupT v v' w → IsLift ht e r v x → IsLift ht e r' v' x' → IsLift ht e s w (cupS h x x') :=
  fun {M _ _ _ i j} h {v v' w x x'} hw hx hx' => ⟨comp_cup h hx.1 hx'.1, fun n =>
    cup_gen ht (B.schFn M.p) (okToOC l K) n h (x n) (x' n) (e M n i (v.lev n)) (e M n j (v'.lev n)) (e M n (i + j) (w.lev n))
      ((congrArg (e M n (i + j)) (hw n)).trans (he.good.cup M n i j (v.lev n) (v'.lev n))) (hx.2 n) (hx'.2 n)⟩

theorem isLift_oneS_of_lev_eq_one (he : EtP e) : ∀ (M : Model l K) (v : M.T 0), (∀ k, v.lev k = GlobalTheory.EtC.one (l ^ k) M.spc) →
    IsLift ht e 0 v (oneS M) := fun M v hv => ⟨comp_one M, fun n =>
  (βF_one (B.schFn M.p) (okToOC l K) ht n).trans
    (congrArg ((tMor ht ((B.schFn M.p).pt (okToOC l K)) 0 n).pull 0) ((congrArg (e M n 0) (hv n)).trans (he.one M n)).symm)⟩

end CrystallineSemistableComparison.HT
end
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers

namespace CrystallineSemistableComparison.HT

open Pb Pb.Lat

theorem dp_of_char {K A B A' B' : Type} [Field K] [CharZero K] [CommRing A] [CommRing B] [CommRing A'] [CommRing B'] [Algebra K B']
    {I : Ideal A} {I' : Ideal A'} {J : Ideal B} {J' : Ideal B'} (δ : DividedPowers J) (δ' : DividedPowers J') (ι : A →+* B)
    (ι' : A' →+* B') (s : A →+* A') (g : B →+* B') (hJ : J = I.map ι) (hJ' : J' = I'.map ι') (hs : I.map s ≤ I')
    (h : ∀ a, g (ι a) = ι' (s a)) : IsDPMorphism δ δ' g := by
  have h1 : J.map g ≤ J' := by
    rw [hJ, hJ', Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
    intro a ha
    change g (ι a) ∈ I'.map ι'
    rw [h]
    exact Ideal.mem_map_of_mem _ (hs (Ideal.mem_map_of_mem _ ha))
  refine ⟨h1, fun {n} a ha => ?_⟩
  have hu : IsUnit (n.factorial : B') := by
    have := (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 n.factorial_ne_zero) : IsUnit (n.factorial : K)).map (algebraMap K B')
    rwa [map_natCast] at this
  refine hu.mul_left_cancel ?_
  rw [δ'.factorial_mul_dpow_eq_pow (h1 (Ideal.mem_map_of_mem _ ha)), ← map_natCast g, ← map_mul, δ.factorial_mul_dpow_eq_pow ha, map_pow]

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ}

theorem levHyp_ex [FiniteDimensional ℚ_[l] K] : ∃ M : ℕ, LevHyp l K M :=
  (GlobalTheory.T.exists_lattice_bound_integers l K).imp fun M h => ⟨h, GlobalTheory.T.acris_mem_lattice_sub l M, GlobalTheory.T.fontaine_lattice_dpow_closed l M, GlobalTheory.T.galois_preserves_t_power_span l K,
    fun k g => GlobalTheory.T.galois_preserves_lattice_sub l K M k g _, GlobalTheory.T.lattice_sub_reduction_mem l M⟩

theorem lev_σ_ι (h : LevHyp l K M) (k : ℕ) (g : K.fixingSubgroup) (a : (lev h k).A) :
    (lev h k).ι ((lev h k).σA g a) = (lev h k).σB g ((lev h k).ι a) :=
  ι_map (fk l k) (xi0 l) (fk l k) (xi0 l) l M (gB h k g) (h.gal k g) a

theorem lev_good (h : LevHyp l K M) (k : ℕ) (hk : 1 ≤ k) : (lev h k).Good := by
  exact {
    pos := hk
    lat := GlobalTheory.T.level_lattice_base h k hk
    toB_surj := GlobalTheory.T.level_toB_surjective h k
    toB_ker := GlobalTheory.T.level_toB_eq_zero_iff_t_pow_dvd h k
    toB_K := GlobalTheory.T.level_toB_algebraMap_field h k
    ι_inj := ι_injective (fk l k) (xi0 l) l M
    ι_dp := dp_ι (fk l k) (xi0 l) l M (h.hc k)
    ι_I := rfl
    IB_eq := GlobalTheory.T.level_ideal_eq_map h k
    ι_O := GlobalTheory.T.level_iota_algebraMap_integers h k
    ι_lam := GlobalTheory.T.level_iota_lam_eq_toB h k
    σB_toB := GlobalTheory.T.level_toB_galois_equivariant h k
    σ_ι := lev_σ_ι h k
    σ_lam := GlobalTheory.T.level_lam_galois_equivariant h k
    σ_O := GlobalTheory.T.level_galois_fixes_integers h k
    σ_dp := GlobalTheory.T.level_galois_isDPMorphism h k
    σB_dp g := dp_of_char (K := K) (lev h k).γB (lev h k).γB (lev h k).ι (lev h k).ι ((lev h k).σA g) ((lev h k).σB g)
      (GlobalTheory.T.level_ideal_eq_map h k) (GlobalTheory.T.level_ideal_eq_map h k) (GlobalTheory.T.level_galois_isDPMorphism h k g).1 fun a => (lev_σ_ι h k g a).symm
    σB_K := GlobalTheory.T.level_galois_fixes_field h k
    pdP_B := GlobalTheory.T.level_filtration_span_t_pow h k
  }

theorem dk_pk (k : ℕ) (x : BdRp l) : dk l k (pk l (k + 1) x) = pk l k x := rfl

theorem sys_dι (h : LevHyp l K M) (m : ℕ) (a : ((levSys h).L (m + 1)).A) :
    (levSys h).dB m (((levSys h).L (m + 1)).ι a) = ((levSys h).L m).ι ((levSys h).dA m a) :=
  (ι_map (fk l (m + 2)) (xi0 l) (fk l (m + 1)) (xi0 l) l M (dk l (m + 1)) (h.dIn (m + 1)) a).symm

theorem levSys_good (h : LevHyp l K M) : (levSys h).Good := by
  exact {
    lev m := lev_good h (m + 1) (Nat.le_add_left 1 m)
    dB_toB m x := dk_pk (m + 1) (pInv l x)
    dι := sys_dι h
    dlam m c := Subtype.ext (dk_pk (m + 1) (ACris.iota ℂ_[l] l c))
    dO m a := Subtype.ext (dk_pk (m + 1) (kP l K a))
    dK m k := dk_pk (m + 1) (kP l K k)
    ddp := GlobalTheory.T.level_system_transition_isDPMorphism h
    ddpB m := dp_of_char (K := K) ((levSys h).L (m + 1)).γB ((levSys h).L m).γB ((levSys h).L (m + 1)).ι ((levSys h).L m).ι
      ((levSys h).dA m) ((levSys h).dB m) (GlobalTheory.T.level_ideal_eq_map h (m + 2)) (GlobalTheory.T.level_ideal_eq_map h (m + 1)) (GlobalTheory.T.level_system_transition_isDPMorphism h m).1 (sys_dι h m)
    dσ := GlobalTheory.T.level_system_transition_galois_A h
    dσB := GlobalTheory.T.level_system_transition_galois_B h
    cpl := GlobalTheory.T.existsUnique_period_of_compatible h
  }

theorem levSys_ex [FiniteDimensional ℚ_[l] K] : ∃ S : Kap.LevSys (per l K), S.Good ∧ ∀ m, (S.L m).CrisOK :=
  (levHyp_ex (l := l) (K := K)).elim fun _ h => ⟨levSys h, levSys_good h, fun m => GlobalTheory.T.level_xi_mem_ideal_and_theta_compat h (m + 1)⟩

end CrystallineSemistableComparison.HT
end
end
