import UnifiedEJM.PhysicsClosureNodes
import UnifiedEJM.PhysicsClosureTerminal

open OddEJM
open scoped BigOperators
namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
open UnifiedEJM.PathCutScore
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open UnifiedEJM.PhysicsEntanglement

theorem nodeIntegerBound0256 : ∀ pen last, terminalScore 256 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 256).parity (tailData 256 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 256 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0201
  · exact terminalBound0559
  · exact terminalBound0560
  · exact terminalBound0561
theorem nodeIntegerBound0257 : ∀ pen last, terminalScore 257 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 257).parity (tailData 257 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 257 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0562
  · exact terminalBound0563
  · exact terminalBound0534
  · exact terminalBound0535
theorem nodeIntegerBound0258 : ∀ pen last, terminalScore 258 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 258).parity (tailData 258 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 258 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0201
  · exact terminalBound0559
  · exact terminalBound0560
  · exact terminalBound0564
theorem nodeIntegerBound0259 : ∀ pen last, terminalScore 259 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 259).parity (tailData 259 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 259 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0158
  · exact terminalBound0545
  · exact terminalBound0158
  · exact terminalBound0159
theorem nodeIntegerBound0260 : ∀ pen last, terminalScore 260 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 260).parity (tailData 260 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 260 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0172
  · exact terminalBound0173
  · exact terminalBound0174
  · exact terminalBound0565
theorem nodeIntegerBound0261 : ∀ pen last, terminalScore 261 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 261).parity (tailData 261 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 261 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0178
  · exact terminalBound0566
  · exact terminalBound0560
  · exact terminalBound0567
theorem nodeIntegerBound0262 : ∀ pen last, terminalScore 262 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 262).parity (tailData 262 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 262 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0536
  · exact terminalBound0537
  · exact terminalBound0538
  · exact terminalBound0568
theorem nodeIntegerBound0263 : ∀ pen last, terminalScore 263 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 263).parity (tailData 263 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 263 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0536
  · exact terminalBound0537
  · exact terminalBound0538
  · exact terminalBound0569
theorem nodeIntegerBound0264 : ∀ pen last, terminalScore 264 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 264).parity (tailData 264 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 264 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0560
  · exact terminalBound0561
  · exact terminalBound0560
  · exact terminalBound0567
theorem nodeIntegerBound0265 : ∀ pen last, terminalScore 265 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 265).parity (tailData 265 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 265 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0536
  · exact terminalBound0570
  · exact terminalBound0571
  · exact terminalBound0572
theorem nodeIntegerBound0266 : ∀ pen last, terminalScore 266 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 266).parity (tailData 266 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 266 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0536
  · exact terminalBound0537
  · exact terminalBound0573
  · exact terminalBound0574
theorem nodeIntegerBound0267 : ∀ pen last, terminalScore 267 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 267).parity (tailData 267 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 267 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0575
  · exact terminalBound0576
  · exact terminalBound0577
  · exact terminalBound0578
theorem nodeIntegerBound0268 : ∀ pen last, terminalScore 268 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 268).parity (tailData 268 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 268 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0536
  · exact terminalBound0537
  · exact terminalBound0571
  · exact terminalBound0579
theorem nodeIntegerBound0269 : ∀ pen last, terminalScore 269 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 269).parity (tailData 269 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 269 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0538
  · exact terminalBound0580
  · exact terminalBound0571
  · exact terminalBound0572
theorem nodeIntegerBound0270 : ∀ pen last, terminalScore 270 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 270).parity (tailData 270 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 270 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0581
  · exact terminalBound0582
  · exact terminalBound0577
  · exact terminalBound0578
theorem nodeIntegerBound0271 : ∀ pen last, terminalScore 271 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 271).parity (tailData 271 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 271 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0560
  · exact terminalBound0583
  · exact terminalBound0180
  · exact terminalBound0181
theorem nodeIntegerBound0272 : ∀ pen last, terminalScore 272 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 272).parity (tailData 272 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 272 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0187
  · exact terminalBound0584
  · exact terminalBound0540
  · exact terminalBound0541
theorem nodeIntegerBound0273 : ∀ pen last, terminalScore 273 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 273).parity (tailData 273 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 273 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0585
  · exact terminalBound0586
  · exact terminalBound0534
  · exact terminalBound0535
theorem nodeIntegerBound0274 : ∀ pen last, terminalScore 274 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 274).parity (tailData 274 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 274 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0587
  · exact terminalBound0588
  · exact terminalBound0589
  · exact terminalBound0590
theorem nodeIntegerBound0275 : ∀ pen last, terminalScore 275 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 275).parity (tailData 275 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 275 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0591
  · exact terminalBound0592
  · exact terminalBound0589
  · exact terminalBound0593
theorem nodeIntegerBound0276 : ∀ pen last, terminalScore 276 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 276).parity (tailData 276 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 276 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0534
  · exact terminalBound0594
  · exact terminalBound0595
  · exact terminalBound0596
theorem nodeIntegerBound0277 : ∀ pen last, terminalScore 277 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 277).parity (tailData 277 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 277 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0536
  · exact terminalBound0597
  · exact terminalBound0538
  · exact terminalBound0598
theorem nodeIntegerBound0278 : ∀ pen last, terminalScore 278 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 278).parity (tailData 278 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 278 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0599
  · exact terminalBound0600
  · exact terminalBound0601
  · exact terminalBound0602
theorem nodeIntegerBound0279 : ∀ pen last, terminalScore 279 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 279).parity (tailData 279 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 279 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0591
  · exact terminalBound0603
  · exact terminalBound0589
  · exact terminalBound0590
theorem nodeIntegerBound0280 : ∀ pen last, terminalScore 280 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 280).parity (tailData 280 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 280 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0585
  · exact terminalBound0604
  · exact terminalBound0595
  · exact terminalBound0596
theorem nodeIntegerBound0281 : ∀ pen last, terminalScore 281 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 281).parity (tailData 281 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 281 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0581
  · exact terminalBound0605
  · exact terminalBound0577
  · exact terminalBound0606
theorem nodeIntegerBound0282 : ∀ pen last, terminalScore 282 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 282).parity (tailData 282 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 282 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0534
  · exact terminalBound0594
  · exact terminalBound0595
  · exact terminalBound0596
theorem nodeIntegerBound0283 : ∀ pen last, terminalScore 283 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 283).parity (tailData 283 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 283 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0543
  · exact terminalBound0607
  · exact terminalBound0595
  · exact terminalBound0596
theorem nodeIntegerBound0284 : ∀ pen last, terminalScore 284 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 284).parity (tailData 284 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 284 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0158
  · exact terminalBound0191
  · exact terminalBound0192
  · exact terminalBound0193
theorem nodeIntegerBound0285 : ∀ pen last, terminalScore 285 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 285).parity (tailData 285 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 285 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0536
  · exact terminalBound0608
  · exact terminalBound0609
  · exact terminalBound0610
theorem nodeIntegerBound0286 : ∀ pen last, terminalScore 286 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 286).parity (tailData 286 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 286 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0536
  · exact terminalBound0608
  · exact terminalBound0538
  · exact terminalBound0611
theorem nodeIntegerBound0287 : ∀ pen last, terminalScore 287 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 287).parity (tailData 287 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 287 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0575
  · exact terminalBound0612
  · exact terminalBound0613
  · exact terminalBound0614
theorem nodeIntegerBound0288 : ∀ pen last, terminalScore 288 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 288).parity (tailData 288 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 288 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0536
  · exact terminalBound0608
  · exact terminalBound0571
  · exact terminalBound0615
theorem nodeIntegerBound0289 : ∀ pen last, terminalScore 289 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 289).parity (tailData 289 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 289 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0591
  · exact terminalBound0592
  · exact terminalBound0616
  · exact terminalBound0617
theorem nodeIntegerBound0290 : ∀ pen last, terminalScore 290 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 290).parity (tailData 290 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 290 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0618
  · exact terminalBound0619
  · exact terminalBound0601
  · exact terminalBound0620
theorem nodeIntegerBound0291 : ∀ pen last, terminalScore 291 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 291).parity (tailData 291 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 291 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0534
  · exact terminalBound0594
  · exact terminalBound0595
  · exact terminalBound0596
theorem nodeIntegerBound0292 : ∀ pen last, terminalScore 292 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 292).parity (tailData 292 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 292 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0587
  · exact terminalBound0621
  · exact terminalBound0616
  · exact terminalBound0617
theorem nodeIntegerBound0293 : ∀ pen last, terminalScore 293 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 293).parity (tailData 293 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 293 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0540
  · exact terminalBound0622
  · exact terminalBound0189
  · exact terminalBound0198
theorem nodeIntegerBound0294 : ∀ pen last, terminalScore 294 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 294).parity (tailData 294 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 294 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0201
  · exact terminalBound0202
  · exact terminalBound0560
  · exact terminalBound0623
theorem nodeIntegerBound0295 : ∀ pen last, terminalScore 295 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 295).parity (tailData 295 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 295 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0581
  · exact terminalBound0605
  · exact terminalBound0613
  · exact terminalBound0614
theorem nodeIntegerBound0296 : ∀ pen last, terminalScore 296 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 296).parity (tailData 296 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 296 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0543
  · exact terminalBound0607
  · exact terminalBound0534
  · exact terminalBound0594
theorem nodeIntegerBound0297 : ∀ pen last, terminalScore 297 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 297).parity (tailData 297 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 297 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0534
  · exact terminalBound0594
  · exact terminalBound0595
  · exact terminalBound0596
theorem nodeIntegerBound0298 : ∀ pen last, terminalScore 298 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 298).parity (tailData 298 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 298 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0562
  · exact terminalBound0624
  · exact terminalBound0595
  · exact terminalBound0596
theorem nodeIntegerBound0299 : ∀ pen last, terminalScore 299 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 299).parity (tailData 299 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 299 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0625
  · exact terminalBound0626
  · exact terminalBound0627
  · exact terminalBound0628
theorem nodeIntegerBound0300 : ∀ pen last, terminalScore 300 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 300).parity (tailData 300 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 300 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0625
  · exact terminalBound0626
  · exact terminalBound0629
  · exact terminalBound0630
theorem nodeIntegerBound0301 : ∀ pen last, terminalScore 301 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 301).parity (tailData 301 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 301 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0631
  · exact terminalBound0632
  · exact terminalBound0213
  · exact terminalBound0214
theorem nodeIntegerBound0302 : ∀ pen last, terminalScore 302 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 302).parity (tailData 302 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 302 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0625
  · exact terminalBound0626
  · exact terminalBound0633
  · exact terminalBound0634
theorem nodeIntegerBound0303 : ∀ pen last, terminalScore 303 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 303).parity (tailData 303 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 303 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0635
  · exact terminalBound0636
  · exact terminalBound0637
  · exact terminalBound0638
theorem nodeIntegerBound0304 : ∀ pen last, terminalScore 304 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 304).parity (tailData 304 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 304 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0633
  · exact terminalBound0634
  · exact terminalBound0627
  · exact terminalBound0628
theorem nodeIntegerBound0305 : ∀ pen last, terminalScore 305 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 305).parity (tailData 305 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 305 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0639
  · exact terminalBound0640
  · exact terminalBound0637
  · exact terminalBound0638
theorem nodeIntegerBound0306 : ∀ pen last, terminalScore 306 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 306).parity (tailData 306 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 306 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0631
  · exact terminalBound0632
  · exact terminalBound0213
  · exact terminalBound0214
theorem nodeIntegerBound0307 : ∀ pen last, terminalScore 307 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 307).parity (tailData 307 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 307 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0221
  · exact terminalBound0222
  · exact terminalBound0641
  · exact terminalBound0642
theorem nodeIntegerBound0308 : ∀ pen last, terminalScore 308 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 308).parity (tailData 308 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 308 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0643
  · exact terminalBound0644
  · exact terminalBound0645
  · exact terminalBound0646
theorem nodeIntegerBound0309 : ∀ pen last, terminalScore 309 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 309).parity (tailData 309 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 309 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0647
  · exact terminalBound0648
  · exact terminalBound0649
  · exact terminalBound0650
theorem nodeIntegerBound0310 : ∀ pen last, terminalScore 310 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 310).parity (tailData 310 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 310 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0651
  · exact terminalBound0652
  · exact terminalBound0653
  · exact terminalBound0654
theorem nodeIntegerBound0311 : ∀ pen last, terminalScore 311 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 311).parity (tailData 311 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 311 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0655
  · exact terminalBound0656
  · exact terminalBound0645
  · exact terminalBound0646
theorem nodeIntegerBound0312 : ∀ pen last, terminalScore 312 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 312).parity (tailData 312 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 312 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0657
  · exact terminalBound0658
  · exact terminalBound0659
  · exact terminalBound0660
theorem nodeIntegerBound0313 : ∀ pen last, terminalScore 313 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 313).parity (tailData 313 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 313 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0651
  · exact terminalBound0652
  · exact terminalBound0649
  · exact terminalBound0650
theorem nodeIntegerBound0314 : ∀ pen last, terminalScore 314 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 314).parity (tailData 314 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 314 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0643
  · exact terminalBound0644
  · exact terminalBound0645
  · exact terminalBound0646
theorem nodeIntegerBound0315 : ∀ pen last, terminalScore 315 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 315).parity (tailData 315 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 315 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0639
  · exact terminalBound0640
  · exact terminalBound0661
  · exact terminalBound0662
theorem nodeIntegerBound0316 : ∀ pen last, terminalScore 316 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 316).parity (tailData 316 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 316 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0655
  · exact terminalBound0656
  · exact terminalBound0645
  · exact terminalBound0646
theorem nodeIntegerBound0317 : ∀ pen last, terminalScore 317 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 317).parity (tailData 317 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 317 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0663
  · exact terminalBound0664
  · exact terminalBound0645
  · exact terminalBound0646
theorem nodeIntegerBound0318 : ∀ pen last, terminalScore 318 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 318).parity (tailData 318 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 318 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0225
  · exact terminalBound0226
  · exact terminalBound0227
  · exact terminalBound0228
theorem nodeIntegerBound0319 : ∀ pen last, terminalScore 319 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 319).parity (tailData 319 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 319 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0625
  · exact terminalBound0626
  · exact terminalBound0665
  · exact terminalBound0666
theorem nodeIntegerBound0320 : ∀ pen last, terminalScore 320 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 320).parity (tailData 320 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 320 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0667
  · exact terminalBound0648
  · exact terminalBound0668
  · exact terminalBound0650
theorem nodeIntegerBound0321 : ∀ pen last, terminalScore 321 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 321).parity (tailData 321 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 321 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0669
  · exact terminalBound0658
  · exact terminalBound0670
  · exact terminalBound0671
theorem nodeIntegerBound0322 : ∀ pen last, terminalScore 322 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 322).parity (tailData 322 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 322 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0672
  · exact terminalBound0656
  · exact terminalBound0673
  · exact terminalBound0646
theorem nodeIntegerBound0323 : ∀ pen last, terminalScore 323 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 323).parity (tailData 323 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 323 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0667
  · exact terminalBound0648
  · exact terminalBound0674
  · exact terminalBound0654
theorem nodeIntegerBound0324 : ∀ pen last, terminalScore 324 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 324).parity (tailData 324 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 324 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0533
  · exact terminalBound0675
  · exact terminalBound0676
  · exact terminalBound0646
theorem nodeIntegerBound0325 : ∀ pen last, terminalScore 325 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 325).parity (tailData 325 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 325 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0677
  · exact terminalBound0634
  · exact terminalBound0678
  · exact terminalBound0666
theorem nodeIntegerBound0326 : ∀ pen last, terminalScore 326 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 326).parity (tailData 326 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 326 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0541
  · exact terminalBound0642
  · exact terminalBound0679
  · exact terminalBound0231
theorem nodeIntegerBound0327 : ∀ pen last, terminalScore 327 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 327).parity (tailData 327 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 327 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0680
  · exact terminalBound0656
  · exact terminalBound0676
  · exact terminalBound0646
theorem nodeIntegerBound0328 : ∀ pen last, terminalScore 328 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 328).parity (tailData 328 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 328 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0545
  · exact terminalBound0226
  · exact terminalBound0234
  · exact terminalBound0228
theorem nodeIntegerBound0329 : ∀ pen last, terminalScore 329 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 329).parity (tailData 329 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 329 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0235
  · exact terminalBound0212
  · exact terminalBound0681
  · exact terminalBound0632
theorem nodeIntegerBound0330 : ∀ pen last, terminalScore 330 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 330).parity (tailData 330 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 330 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0682
  · exact terminalBound0636
  · exact terminalBound0683
  · exact terminalBound0638
theorem nodeIntegerBound0331 : ∀ pen last, terminalScore 331 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 331).parity (tailData 331 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 331 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0684
  · exact terminalBound0644
  · exact terminalBound0685
  · exact terminalBound0656
theorem nodeIntegerBound0332 : ∀ pen last, terminalScore 332 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 332).parity (tailData 332 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 332 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0556
  · exact terminalBound0644
  · exact terminalBound0676
  · exact terminalBound0646
theorem nodeIntegerBound0333 : ∀ pen last, terminalScore 333 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 333).parity (tailData 333 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 333 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0682
  · exact terminalBound0636
  · exact terminalBound0686
  · exact terminalBound0662
theorem nodeIntegerBound0334 : ∀ pen last, terminalScore 334 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 334).parity (tailData 334 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 334 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0533
  · exact terminalBound0675
  · exact terminalBound0676
  · exact terminalBound0646
theorem nodeIntegerBound0335 : ∀ pen last, terminalScore 335 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 335).parity (tailData 335 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 335 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0684
  · exact terminalBound0644
  · exact terminalBound0687
  · exact terminalBound0646
theorem nodeIntegerBound0336 : ∀ pen last, terminalScore 336 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 336).parity (tailData 336 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 336 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0545
  · exact terminalBound0226
  · exact terminalBound0234
  · exact terminalBound0228
theorem nodeIntegerBound0337 : ∀ pen last, terminalScore 337 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 337).parity (tailData 337 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 337 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0688
  · exact terminalBound0632
  · exact terminalBound0561
  · exact terminalBound0632
theorem nodeIntegerBound0338 : ∀ pen last, terminalScore 338 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 338).parity (tailData 338 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 338 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0689
  · exact terminalBound0656
  · exact terminalBound0676
  · exact terminalBound0646
theorem nodeIntegerBound0339 : ∀ pen last, terminalScore 339 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 339).parity (tailData 339 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 339 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0688
  · exact terminalBound0632
  · exact terminalBound0690
  · exact terminalBound0237
theorem nodeIntegerBound0340 : ∀ pen last, terminalScore 340 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 340).parity (tailData 340 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 340 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0545
  · exact terminalBound0226
  · exact terminalBound0234
  · exact terminalBound0228
theorem nodeIntegerBound0341 : ∀ pen last, terminalScore 341 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 341).parity (tailData 341 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 341 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0242
  · exact terminalBound0210
  · exact terminalBound0565
  · exact terminalBound0210
theorem nodeIntegerBound0342 : ∀ pen last, terminalScore 342 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 342).parity (tailData 342 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 342 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0691
  · exact terminalBound0632
  · exact terminalBound0692
  · exact terminalBound0214
theorem nodeIntegerBound0343 : ∀ pen last, terminalScore 343 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 343).parity (tailData 343 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 343 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0677
  · exact terminalBound0634
  · exact terminalBound0693
  · exact terminalBound0628
theorem nodeIntegerBound0344 : ∀ pen last, terminalScore 344 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 344).parity (tailData 344 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 344 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0677
  · exact terminalBound0634
  · exact terminalBound0694
  · exact terminalBound0630
theorem nodeIntegerBound0345 : ∀ pen last, terminalScore 345 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 345).parity (tailData 345 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 345 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0561
  · exact terminalBound0632
  · exact terminalBound0692
  · exact terminalBound0214
theorem nodeIntegerBound0346 : ∀ pen last, terminalScore 346 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 346).parity (tailData 346 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 346 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0695
  · exact terminalBound0696
  · exact terminalBound0697
  · exact terminalBound0698
theorem nodeIntegerBound0347 : ∀ pen last, terminalScore 347 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 347).parity (tailData 347 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 347 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0677
  · exact terminalBound0634
  · exact terminalBound0574
  · exact terminalBound0699
theorem nodeIntegerBound0348 : ∀ pen last, terminalScore 348 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 348).parity (tailData 348 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 348 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0700
  · exact terminalBound0701
  · exact terminalBound0702
  · exact terminalBound0703
theorem nodeIntegerBound0349 : ∀ pen last, terminalScore 349 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 349).parity (tailData 349 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 349 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0677
  · exact terminalBound0634
  · exact terminalBound0579
  · exact terminalBound0704
theorem nodeIntegerBound0350 : ∀ pen last, terminalScore 350 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 350).parity (tailData 350 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 350 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0705
  · exact terminalBound0696
  · exact terminalBound0697
  · exact terminalBound0698
theorem nodeIntegerBound0351 : ∀ pen last, terminalScore 351 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 351).parity (tailData 351 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 351 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0706
  · exact terminalBound0701
  · exact terminalBound0702
  · exact terminalBound0703
theorem nodeIntegerBound0352 : ∀ pen last, terminalScore 352 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 352).parity (tailData 352 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 352 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0707
  · exact terminalBound0248
  · exact terminalBound0249
  · exact terminalBound0250
theorem nodeIntegerBound0353 : ∀ pen last, terminalScore 353 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 353).parity (tailData 353 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 353 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0708
  · exact terminalBound0642
  · exact terminalBound0541
  · exact terminalBound0642
theorem nodeIntegerBound0354 : ∀ pen last, terminalScore 354 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 354).parity (tailData 354 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 354 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0709
  · exact terminalBound0656
  · exact terminalBound0676
  · exact terminalBound0646
theorem nodeIntegerBound0355 : ∀ pen last, terminalScore 355 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 355).parity (tailData 355 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 355 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0710
  · exact terminalBound0711
  · exact terminalBound0712
  · exact terminalBound0713
theorem nodeIntegerBound0356 : ∀ pen last, terminalScore 356 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 356).parity (tailData 356 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 356 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0714
  · exact terminalBound0715
  · exact terminalBound0716
  · exact terminalBound0717
theorem nodeIntegerBound0357 : ∀ pen last, terminalScore 357 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 357).parity (tailData 357 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 357 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0718
  · exact terminalBound0719
  · exact terminalBound0720
  · exact terminalBound0721
theorem nodeIntegerBound0358 : ∀ pen last, terminalScore 358 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 358).parity (tailData 358 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 358 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0722
  · exact terminalBound0723
  · exact terminalBound0724
  · exact terminalBound0723
theorem nodeIntegerBound0359 : ∀ pen last, terminalScore 359 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 359).parity (tailData 359 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 359 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0725
  · exact terminalBound0726
  · exact terminalBound0727
  · exact terminalBound0728
theorem nodeIntegerBound0360 : ∀ pen last, terminalScore 360 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 360).parity (tailData 360 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 360 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0729
  · exact terminalBound0711
  · exact terminalBound0712
  · exact terminalBound0713
theorem nodeIntegerBound0361 : ∀ pen last, terminalScore 361 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 361).parity (tailData 361 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 361 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0730
  · exact terminalBound0719
  · exact terminalBound0720
  · exact terminalBound0721
theorem nodeIntegerBound0362 : ∀ pen last, terminalScore 362 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 362).parity (tailData 362 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 362 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0731
  · exact terminalBound0732
  · exact terminalBound0733
  · exact terminalBound0734
theorem nodeIntegerBound0363 : ∀ pen last, terminalScore 363 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 363).parity (tailData 363 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 363 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0718
  · exact terminalBound0719
  · exact terminalBound0720
  · exact terminalBound0721
theorem nodeIntegerBound0364 : ∀ pen last, terminalScore 364 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 364).parity (tailData 364 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 364 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0735
  · exact terminalBound0719
  · exact terminalBound0720
  · exact terminalBound0721
theorem nodeIntegerBound0365 : ∀ pen last, terminalScore 365 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 365).parity (tailData 365 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 365 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0260
  · exact terminalBound0261
  · exact terminalBound0262
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
theorem nodeIntegerBound0366 : ∀ pen last, terminalScore 366 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 366).parity (tailData 366 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 366 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0736
  · exact terminalBound0737
  · exact terminalBound0738
  · exact terminalBound0739
theorem nodeIntegerBound0367 : ∀ pen last, terminalScore 367 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 367).parity (tailData 367 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 367 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0736
  · exact terminalBound0737
  · exact terminalBound0740
  · exact terminalBound0737
theorem nodeIntegerBound0368 : ∀ pen last, terminalScore 368 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 368).parity (tailData 368 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 368 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0741
  · exact terminalBound0732
  · exact terminalBound0742
  · exact terminalBound0743
theorem nodeIntegerBound0369 : ∀ pen last, terminalScore 369 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 369).parity (tailData 369 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 369 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0736
  · exact terminalBound0737
  · exact terminalBound0744
  · exact terminalBound0745
theorem nodeIntegerBound0370 : ∀ pen last, terminalScore 370 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 370).parity (tailData 370 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 370 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0714
  · exact terminalBound0715
  · exact terminalBound0746
  · exact terminalBound0747
theorem nodeIntegerBound0371 : ∀ pen last, terminalScore 371 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 371).parity (tailData 371 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 371 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0748
  · exact terminalBound0749
  · exact terminalBound0750
  · exact terminalBound0751
theorem nodeIntegerBound0372 : ∀ pen last, terminalScore 372 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 372).parity (tailData 372 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 372 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0718
  · exact terminalBound0719
  · exact terminalBound0720
  · exact terminalBound0721
theorem nodeIntegerBound0373 : ∀ pen last, terminalScore 373 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 373).parity (tailData 373 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 373 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0752
  · exact terminalBound0715
  · exact terminalBound0746
  · exact terminalBound0747
theorem nodeIntegerBound0374 : ∀ pen last, terminalScore 374 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 374).parity (tailData 374 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 374 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0753
  · exact terminalBound0266
  · exact terminalBound0267
  · exact terminalBound0268
theorem nodeIntegerBound0375 : ∀ pen last, terminalScore 375 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 375).parity (tailData 375 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 375 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · norm_num [terminalScore, nodeScan, nodeData, scanStep, scoreStep] at hscore
  · exact terminalBound0271
  · exact terminalBound0754
  · exact terminalBound0271
theorem nodeIntegerBound0376 : ∀ pen last, terminalScore 376 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 376).parity (tailData 376 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 376 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0731
  · exact terminalBound0732
  · exact terminalBound0742
  · exact terminalBound0743
theorem nodeIntegerBound0377 : ∀ pen last, terminalScore 377 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 377).parity (tailData 377 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 377 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0735
  · exact terminalBound0719
  · exact terminalBound0718
  · exact terminalBound0719
theorem nodeIntegerBound0378 : ∀ pen last, terminalScore 378 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 378).parity (tailData 378 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 378 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0718
  · exact terminalBound0719
  · exact terminalBound0720
  · exact terminalBound0721
theorem nodeIntegerBound0379 : ∀ pen last, terminalScore 379 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 379).parity (tailData 379 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 379 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0755
  · exact terminalBound0719
  · exact terminalBound0720
  · exact terminalBound0721
theorem nodeIntegerBound0380 : ∀ pen last, terminalScore 380 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 380).parity (tailData 380 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 380 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0278
  · exact terminalBound0279
  · exact terminalBound0280
  · exact terminalBound0756
theorem nodeIntegerBound0381 : ∀ pen last, terminalScore 381 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 381).parity (tailData 381 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 381 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0757
  · exact terminalBound0758
  · exact terminalBound0759
  · exact terminalBound0760
theorem nodeIntegerBound0382 : ∀ pen last, terminalScore 382 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 382).parity (tailData 382 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 382 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0280
  · exact terminalBound0756
  · exact terminalBound0280
  · exact terminalBound0281
theorem nodeIntegerBound0383 : ∀ pen last, terminalScore 383 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 383).parity (tailData 383 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 383 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0761
  · exact terminalBound0762
  · exact terminalBound0759
  · exact terminalBound0760

end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
