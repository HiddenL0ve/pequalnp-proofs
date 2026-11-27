import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.LowMergeWires
import PEqualNP.Outside.L_meta_30581
import PEqualNP.Outside.L_meta_17187

namespace PEqualNP.MetaComplexity.FourMissingPairs

open CircuitLowerBounds
open Represents (oneEach Represents RepSizeAtMost)
open MetaComplexity (Monotone2)

/-- Raw inputs outside the retained banks go to a wire beyond the whole new circuit.
Gate indices keep their offset from the end of the raw inputs. -/
private def wire (n m a b dead w : Nat) : Nat :=
  if w < n then (if w < a then w else dead)
  else if w < n + m then (if w - n < b then a + (w - n) else dead)
  else a + b + (w - (n + m))

private def rename (r : Nat → Nat) (g : Gate) : Gate := ⟨g.op, g.inputs.map r⟩

private def step (ws : List Bool) (g : Gate) : List Bool :=
  ws ++ [g.op.eval (g.inputs.map fun k => ws.getD k false)]

private theorem lengthInput {a b : Nat} (u : Fin a) (v : Fin b) : (oneEach u v).length = a + b := by
  simp [oneEach]

private theorem readInput {a b : Nat} (u : Fin a) (v : Fin b) (i : Nat) :
    (oneEach u v).getD i false = decide (i = u.val ∨ i = a + v.val) := by
  have hu := u.isLt
  have hv := v.isLt
  unfold oneEach
  by_cases hi : i < a
  · rw [List.getD_append _ _ _ _ (by simpa using hi)]
    simp [List.getD_eq_getElem?_getD, hi, Fin.ext_iff, show i ≠ a + v.val by omega]
  · rw [List.getD_append_right _ _ _ _ (by simp; omega), List.length_ofFn]
    by_cases hj : i - a < b
    · simp [List.getD_eq_getElem?_getD, hj, Fin.ext_iff, show i ≠ u.val by omega,
        show i - a = v.val ↔ i = a + v.val by omega]
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      simp [show i ≠ u.val by omega, show i ≠ a + v.val by omega]

private theorem readPrefix {n m a b N : Nat} (ha : a ≤ n) (hb : b ≤ m)
    (u : Fin a) (v : Fin b) (tail : List Bool) (ht : tail.length ≤ N) (w : Nat) :
    (oneEach u v ++ tail).getD (wire n m a b (a + b + N) w) false =
    (oneEach (Fin.castLE ha u) (Fin.castLE hb v) ++ tail).getD w false := by
  have hu := u.isLt
  have hv := v.isLt
  by_cases raw : w < n + m
  · conv_rhs => rw [List.getD_append _ _ _ _ (by rwa [lengthInput]), readInput]
    simp only [Fin.val_castLE]
    by_cases left : w < n
    · by_cases kept : w < a
      · simp only [wire, if_pos left, if_pos kept]
        rw [List.getD_append _ _ _ _ (by rw [lengthInput]; omega), readInput]
        simp [show w ≠ a + v.val by omega, show w ≠ n + v.val by omega]
      · simp only [wire, if_pos left, if_neg kept]
        rw [List.getD_eq_default _ _ (by rw [List.length_append, lengthInput]; omega)]
        simp [show w ≠ u.val by omega, show w ≠ n + v.val by omega]
    · by_cases kept : w - n < b
      · simp only [wire, if_neg left, if_pos raw, if_pos kept]
        rw [List.getD_append _ _ _ _ (by rw [lengthInput]; omega), readInput]
        simp [show a + (w - n) ≠ u.val by omega, show w ≠ u.val by omega,
          show a + (w - n) = a + v.val ↔ w = n + v.val by omega] <;> omega
      · simp only [wire, if_neg left, if_pos raw, if_neg kept]
        rw [List.getD_eq_default _ _ (by rw [List.length_append, lengthInput]; omega)]
        simp [show w ≠ u.val by omega, show w ≠ n + v.val by omega]
  · simp only [wire, if_neg (show ¬ w < n by omega), if_neg raw]
    rw [List.getD_append_right _ _ _ _ (by rw [lengthInput]; omega),
      List.getD_append_right _ _ _ _ (by rw [lengthInput]; omega), lengthInput, lengthInput]
    congr 1
    omega

private theorem simulation {n m a b N : Nat} (ha : a ≤ n) (hb : b ≤ m)
    (u : Fin a) (v : Fin b) (gs : List Gate) (tail : List Bool) (h : tail.length + gs.length ≤ N) :
    let r := wire n m a b (a + b + N)
    ∃ out : List Bool, out.length ≤ N ∧
      (gs.map (rename r)).foldl step (oneEach u v ++ tail) = oneEach u v ++ out ∧
      gs.foldl step (oneEach (Fin.castLE ha u) (Fin.castLE hb v) ++ tail) =
        oneEach (Fin.castLE ha u) (Fin.castLE hb v) ++ out := by
  induction gs generalizing tail with
  | nil => exact ⟨tail, by simpa using h, rfl, rfl⟩
  | cons g rest ih =>
    let old := oneEach (Fin.castLE ha u) (Fin.castLE hb v) ++ tail
    let bit := g.op.eval (g.inputs.map fun k => old.getD k false)
    have ht : tail.length ≤ N := by omega
    have same : (rename (wire n m a b (a + b + N)) g).op.eval
        ((rename (wire n m a b (a + b + N)) g).inputs.map fun k =>
          (oneEach u v ++ tail).getD k false) = bit := by
      simp only [rename, List.map_map, Function.comp_def, readPrefix ha hb u v tail ht, bit, old]
    have bound : (tail ++ [bit]).length + rest.length ≤ N := by
      simp only [List.length_cons] at h
      simp; omega
    simpa only [List.map_cons, List.foldl_cons, step, same, List.append_assoc, bit, old]
      using ih (tail ++ [bit]) bound

/-- A prefix restriction keeps the gate list's operations and arities, including the NOT count. -/
private theorem restrictCircuit {n m a b : Nat} (ha : a ≤ n) (hb : b ≤ m)
    (A : Fin n → Fin m → Bool) (C : Circuit) (rep : Represents A C) :
    ∃ D : Circuit, D.size = C.size ∧
      (MetaComplexity.FanInTwo C → MetaComplexity.FanInTwo D) ∧
      (Monotone2 C → Monotone2 D) ∧ NotBracket.notCount D = NotBracket.notCount C ∧
      Represents (fun i j => A (Fin.castLE ha i) (Fin.castLE hb j)) D := by
  let r := wire n m a b (a + b + C.size)
  let D : Circuit := ⟨C.gates.map (rename r), r C.output⟩
  refine ⟨D, by simp [D, Circuit.size], ?_, ?_, ?_, ?_⟩
  · intro ops g hg
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hg
    simpa [rename] using ops f hf
  · intro mono g hg
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hg
    simpa [rename] using mono f hf
  · unfold NotBracket.notCount
    simp [D, List.filter_map, Function.comp_def, rename]
    congr 2
  · intro u v
    obtain ⟨out, len, hnew, hold⟩ :=
      simulation (N := C.size) ha hb u v C.gates [] (by simp [Circuit.size])
    simp only [List.append_nil] at hnew hold
    have val := rep (Fin.castLE ha u) (Fin.castLE hb v)
    change (C.gates.foldl step _).getD C.output false = _ at val
    change ((C.gates.map (rename r)).foldl step _).getD (r C.output) false = _
    rw [hnew, readPrefix ha hb u v out len, ← hold, val]

end PEqualNP.MetaComplexity.FourMissingPairs

namespace PEqualNP.MetaComplexity.OutputNegation

open CircuitLowerBounds
open PEqualNP.Represents (Represents)

private def flipOutput (inputs : Nat) (C : Circuit) : Circuit :=
  ⟨C.gates ++ [⟨.not, [C.output]⟩], inputs + C.size⟩

private theorem flip_spec {n m : Nat} {C : Circuit} {A : Fin n → Fin m → Bool}
    (ops : FanInTwo C) (rep : Represents A C) :
    FanInTwo (flipOutput (n + m) C) ∧ (flipOutput (n + m) C).size = C.size + 1 ∧
      Represents (fun u v => !(A u v)) (flipOutput (n + m) C) := by
  refine ⟨?_, by simp [flipOutput, Circuit.size], ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with old | last
    · exact ops g old
    · obtain rfl := List.mem_singleton.mp last
      simp
  · intro u v
    let x := PEqualNP.Represents.oneEach u v
    have length : (C.wires x).length = n + m + C.size := by
      simp [LowMergeProof.wires_length, x, PEqualNP.Represents.oneEach, Circuit.size]
    change ((flipOutput (n + m) C).wires x).getD (n + m + C.size) false = !(A u v)
    have wires : (flipOutput (n + m) C).wires x = C.wires x ++ [!(C.eval x)] := by
      simp [flipOutput, Circuit.wires, Circuit.eval, List.foldl_append, GateOp.eval]
    rw [wires, ← length, List.getD_append_right _ _ _ _ (le_refl _)]
    simpa [x] using congrArg Bool.not (rep u v)

private theorem monoFanInTwo {C : Circuit} (h : Monotone2 C) : FanInTwo C := by
  intro g hg
  obtain ⟨kind, width⟩ := h g hg
  refine ⟨?_, width⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at kind ⊢
  tauto

end PEqualNP.MetaComplexity.OutputNegation

namespace PEqualNP.MetaComplexity.ThreeDiagonalCosts

open CircuitLowerBounds OutputNegation
open PEqualNP.Represents (Represents RepSizeAtMost oneEach)

attribute [local instance] lineDegreeGateOpDecEq

/-- All cells except the first three diagonal cells, in the registry's mask encoding. -/
private abbrev dense {n m : Nat} (u : Fin n) (v : Fin m) : Bool :=
  (64478 : Nat).testBit (4 * min u.val 3 + min v.val 3)

private def diagonal (a b : Nat) : Bool :=
  ((decide (0 = a) && decide (0 = b)) || (decide (1 = a) && decide (1 = b))) ||
    (decide (2 = a) && decide (2 = b))

private theorem maskComplement (a b : Nat) :
    diagonal a b = !((64478 : Nat).testBit (4 * min a 3 + min b 3)) := by
  have table : ∀ i j : Fin 4, diagonal i.val j.val = !((64478 : Nat).testBit (4*i.val+j.val)) :=
    by decide +kernel
  have t := table ⟨min a 3, by omega⟩ ⟨min b 3, by omega⟩
  have cut (x k : Nat) (hk : k < 3) : (k = min x 3) ↔ k = x := by omega
  simpa only [diagonal, cut a 0 (by decide), cut a 1 (by decide), cut a 2 (by decide),
    cut b 0 (by decide), cut b 1 (by decide), cut b 2 (by decide)] using t

/-- Three AND gates test the specified cells and two OR gates combine them. -/
private def readDiagonal (n m : Nat) : Circuit :=
  let N := n + m
  ⟨[⟨.and, [0,n]⟩, ⟨.and, [1,n+1]⟩, ⟨.and, [2,n+2]⟩,
    ⟨.or, [N,N+1]⟩, ⟨.or, [N+3,N+2]⟩], N+4⟩

private theorem fiveGates {n m : Nat} (hn : 3 ≤ n) (hm : 3 ≤ m) :
    let C := readDiagonal n m
    Monotone2 C ∧ C.size = 5 ∧ Represents (fun (u : Fin n) (v : Fin m) => !(dense u v)) C := by
  refine ⟨?_, rfl, ?_⟩
  · simp [Monotone2, readDiagonal]
  · intro u v
    let x := oneEach u v
    have len : x.length = n + m := by simp [x, oneEach]
    have row (i : Nat) (hi : i < n) : x.getD i false = decide (i = u.val) := by
      dsimp [x, oneEach]
      rw [List.getD_append _ _ _ _ (by simpa using hi)]
      simp [List.getD_eq_getElem?_getD, hi, Fin.ext_iff]
    have col (j : Nat) (hj : j < m) : x.getD (n+j) false = decide (j = v.val) := by
      dsimp [x, oneEach]
      rw [List.getD_append_right _ _ _ _ (by simp)]
      simp [List.getD_eq_getElem?_getD, hj, Fin.ext_iff]
    have col0 : x.getD n false = decide (0 = v.val) := by simpa using col 0 (by omega)
    have raw (w : List Bool) (i : Nat) (hi : i < n + m) :
        (x ++ w).getD i false = x.getD i false :=
      List.getD_append _ _ _ _ (by omega)
    have gate (w : List Bool) (j : Nat) :
        (x ++ w).getD (n + m + j) false = w.getD j false := by
      rw [List.getD_append_right _ _ _ _ (by omega), len]
      congr 1
      omega
    have first (w : List Bool) : (x ++ w).getD (n + m) false = w.getD 0 false := gate w 0
    change ((readDiagonal n m).wires x).getD (n+m+4) false = _
    refine Eq.trans ?_ (maskComplement u.val v.val)
    simp (disch := omega) only [readDiagonal, Circuit.wires, GateOp.eval, List.foldl_cons,
      List.foldl_nil, List.map_cons, List.map_nil, List.any_cons, List.any_nil, List.all_cons,
      List.all_nil, id_eq, Bool.or_false, Bool.and_true, List.append_assoc, List.cons_append,
      List.nil_append, gate, first, raw, row, col0, col]
    rfl

/-- Restriction to the first three rows and columns transfers the matching bound. -/
private theorem sixFloor {n m : Nat} (hn : 3 ≤ n) (hm : 3 ≤ m)
    (crown : ∀ C : Circuit, FanInTwo C → Represents (fun u v : Fin 3 => decide (u ≠ v)) C →
      6 ≤ C.size) (C : Circuit) (ops : FanInTwo C) (rep : Represents (@dense n m) C) :
    6 ≤ C.size := by
  obtain ⟨D, size, keep, _, _, represents⟩ := FourMissingPairs.restrictCircuit hn hm _ C rep
  have cells : ∀ u v : Fin 3, dense u v = decide (u ≠ v) := by decide +kernel
  rw [← size]
  exact crown D (keep ops) (fun u v => (represents u v).trans (cells u v))

/-- All three gate budgets. The sparse complement costs five even with unrestricted NOTs.
A single NOT suffices for the six-gate optimum on the dense board. -/
private theorem costs {n m : Nat} (hn : 3 ≤ n) (hm : 3 ≤ m)
    (mono : RepSizeAtMost (@dense n m) (n+m+1) ∧ ¬ RepSizeAtMost (@dense n m) (n+m))
    (crown : ∀ C : Circuit, FanInTwo C → Represents (fun u v : Fin 3 => decide (u ≠ v)) C →
      6 ≤ C.size) (s k : Nat) (hk : 1 ≤ k) :
    let A := @dense n m
    let B := fun u v => !(A u v)
    (RepSizeAtMost A s ↔ n+m+1 ≤ s) ∧
    ((∃ C : Circuit, FanInTwo C ∧ C.size ≤ s ∧ NotBracket.notCount C ≤ k ∧ Represents A C) ↔
      6 ≤ s) ∧
    ((∃ C : Circuit, FanInTwo C ∧ C.size ≤ s ∧ Represents A C) ↔ 6 ≤ s) ∧
    (RepSizeAtMost B s ↔ 5 ≤ s) ∧
    ((∃ C : Circuit, FanInTwo C ∧ C.size ≤ s ∧ Represents B C) ↔ 5 ≤ s) := by
  dsimp only
  obtain ⟨gates, sz, rep⟩ := fiveGates hn hm
  let F := flipOutput (n+m) (readDiagonal n m)
  obtain ⟨fops, fsz, fval⟩ := flip_spec (monoFanInTwo gates) rep
  have frep : Represents (@dense n m) F := by simpa [F] using fval
  have fcount : NotBracket.notCount F = 1 := rfl
  have denseLower := sixFloor hn hm crown
  have sparseLower (C : Circuit) (ops : FanInTwo C)
      (repC : Represents (fun (u : Fin n) (v : Fin m) => !(dense u v)) C) : 5 ≤ C.size := by
    obtain ⟨fops', sz', rep'⟩ := flip_spec ops repC
    have h := denseLower _ fops' (by simpa using rep')
    omega
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro ⟨C, ops, size, repr⟩
    by_contra! small
    exact mono.2 ⟨C, ops, by omega, repr⟩
  · intro enough
    obtain ⟨C, ops, size, repr⟩ := mono.1
    exact ⟨C, ops, size.trans enough, repr⟩
  · rintro ⟨C, ops, size, _, repr⟩
    exact (denseLower C ops repr).trans size
  · intro enough
    exact ⟨F, fops, by dsimp [F]; omega, fcount.trans_le hk, frep⟩
  · rintro ⟨C, ops, size, repr⟩
    exact (denseLower C ops repr).trans size
  · intro enough
    exact ⟨F, fops, by dsimp [F]; omega, frep⟩
  · rintro ⟨C, ops, size, repr⟩
    exact (sparseLower C (monoFanInTwo ops) repr).trans size
  · intro enough
    exact ⟨_, gates, sz.trans_le enough, rep⟩
  · rintro ⟨C, ops, size, repr⟩
    exact (sparseLower C ops repr).trans size
  · intro enough
    exact ⟨_, monoFanInTwo gates, sz.trans_le enough, rep⟩

end PEqualNP.MetaComplexity.ThreeDiagonalCosts

theorem PEqualNP.Outside.L_meta_33675 :
∀ (n m : Nat), 3 ≤ n → 3 ≤ m →
  let A := fun (i : Fin n) (j : Fin m) =>
    (64478 : Nat).testBit (4 * min i.val 3 + min j.val 3)
  let B := fun (i : Fin n) (j : Fin m) => !(A i j)
  ∀ (s k : Nat), 1 ≤ k →
    (PEqualNP.Represents.RepSizeAtMost A s ↔ n + m + 1 ≤ s) ∧
    ((∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧
      C.size ≤ s ∧ PEqualNP.NotBracket.notCount C ≤ k ∧ PEqualNP.Represents.Represents A C)
      ↔ 6 ≤ s) ∧
    ((∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧
      C.size ≤ s ∧ PEqualNP.Represents.Represents A C) ↔ 6 ≤ s) ∧
    (PEqualNP.Represents.RepSizeAtMost B s ↔ 5 ≤ s) ∧
    ((∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧
      C.size ≤ s ∧ PEqualNP.Represents.Represents B C) ↔ 5 ≤ s) := by
  intro n m hn hm
  dsimp only
  intro s k hk
  exact PEqualNP.MetaComplexity.ThreeDiagonalCosts.costs hn hm (PEqualNP.Outside.L_meta_30581 n m hn hm)
    (PEqualNP.Outside.L_meta_17187 3 (by decide)) s k hk
