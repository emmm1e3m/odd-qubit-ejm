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

theorem nodeIntegerBound1280 : ∀ pen last, terminalScore 1280 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1280).parity (tailData 1280 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1280 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1252
  · exact terminalBound1253
  · exact terminalBound1832
  · exact terminalBound1833
theorem nodeIntegerBound1281 : ∀ pen last, terminalScore 1281 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1281).parity (tailData 1281 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1281 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1832
  · exact terminalBound1833
  · exact terminalBound1250
  · exact terminalBound1251
theorem nodeIntegerBound1282 : ∀ pen last, terminalScore 1282 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1282).parity (tailData 1282 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1282 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1836
  · exact terminalBound1837
  · exact terminalBound1838
  · exact terminalBound1839
theorem nodeIntegerBound1283 : ∀ pen last, terminalScore 1283 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1283).parity (tailData 1283 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1283 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1832
  · exact terminalBound1833
  · exact terminalBound1250
  · exact terminalBound1251
theorem nodeIntegerBound1284 : ∀ pen last, terminalScore 1284 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1284).parity (tailData 1284 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1284 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1270
  · exact terminalBound1271
  · exact terminalBound1840
  · exact terminalBound1841
theorem nodeIntegerBound1285 : ∀ pen last, terminalScore 1285 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1285).parity (tailData 1285 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1285 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1842
  · exact terminalBound1843
  · exact terminalBound1844
  · exact terminalBound1845
theorem nodeIntegerBound1286 : ∀ pen last, terminalScore 1286 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1286).parity (tailData 1286 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1286 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1828
  · exact terminalBound1829
  · exact terminalBound1846
  · exact terminalBound1847
theorem nodeIntegerBound1287 : ∀ pen last, terminalScore 1287 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1287).parity (tailData 1287 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1287 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1840
  · exact terminalBound1841
  · exact terminalBound1278
  · exact terminalBound1279
theorem nodeIntegerBound1288 : ∀ pen last, terminalScore 1288 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1288).parity (tailData 1288 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1288 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1848
  · exact terminalBound1849
  · exact terminalBound1844
  · exact terminalBound1845
theorem nodeIntegerBound1289 : ∀ pen last, terminalScore 1289 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1289).parity (tailData 1289 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1289 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1274
  · exact terminalBound1275
  · exact terminalBound1258
  · exact terminalBound1259
theorem nodeIntegerBound1290 : ∀ pen last, terminalScore 1290 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1290).parity (tailData 1290 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1290 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1266
  · exact terminalBound1267
  · exact terminalBound1850
  · exact terminalBound1851
theorem nodeIntegerBound1291 : ∀ pen last, terminalScore 1291 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1291).parity (tailData 1291 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1291 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1852
  · exact terminalBound1853
  · exact terminalBound1844
  · exact terminalBound1845
theorem nodeIntegerBound1292 : ∀ pen last, terminalScore 1292 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1292).parity (tailData 1292 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1292 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1842
  · exact terminalBound1843
  · exact terminalBound1844
  · exact terminalBound1845
theorem nodeIntegerBound1293 : ∀ pen last, terminalScore 1293 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1293).parity (tailData 1293 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1293 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1854
  · exact terminalBound1855
  · exact terminalBound1844
  · exact terminalBound1845
theorem nodeIntegerBound1294 : ∀ pen last, terminalScore 1294 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1294).parity (tailData 1294 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1294 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1856
  · exact terminalBound1857
  · exact terminalBound1858
  · exact terminalBound1859
theorem nodeIntegerBound1295 : ∀ pen last, terminalScore 1295 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1295).parity (tailData 1295 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1295 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1860
  · exact terminalBound1861
  · exact terminalBound1844
  · exact terminalBound1845
theorem nodeIntegerBound1296 : ∀ pen last, terminalScore 1296 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1296).parity (tailData 1296 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1296 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1856
  · exact terminalBound1857
  · exact terminalBound1862
  · exact terminalBound1863
theorem nodeIntegerBound1297 : ∀ pen last, terminalScore 1297 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1297).parity (tailData 1297 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1297 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1842
  · exact terminalBound1843
  · exact terminalBound1844
  · exact terminalBound1845
theorem nodeIntegerBound1298 : ∀ pen last, terminalScore 1298 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1298).parity (tailData 1298 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1298 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1836
  · exact terminalBound1837
  · exact terminalBound1864
  · exact terminalBound1865
theorem nodeIntegerBound1299 : ∀ pen last, terminalScore 1299 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1299).parity (tailData 1299 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1299 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1860
  · exact terminalBound1861
  · exact terminalBound1844
  · exact terminalBound1845
theorem nodeIntegerBound1300 : ∀ pen last, terminalScore 1300 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1300).parity (tailData 1300 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1300 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1866
  · exact terminalBound1867
  · exact terminalBound1868
  · exact terminalBound1869
theorem nodeIntegerBound1301 : ∀ pen last, terminalScore 1301 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1301).parity (tailData 1301 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1301 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1860
  · exact terminalBound1861
  · exact terminalBound1844
  · exact terminalBound1845
theorem nodeIntegerBound1302 : ∀ pen last, terminalScore 1302 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1302).parity (tailData 1302 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1302 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1848
  · exact terminalBound1849
  · exact terminalBound1860
  · exact terminalBound1861
theorem nodeIntegerBound1303 : ∀ pen last, terminalScore 1303 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1303).parity (tailData 1303 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1303 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1860
  · exact terminalBound1861
  · exact terminalBound1844
  · exact terminalBound1845
theorem nodeIntegerBound1304 : ∀ pen last, terminalScore 1304 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1304).parity (tailData 1304 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1304 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1866
  · exact terminalBound1867
  · exact terminalBound1870
  · exact terminalBound1871
theorem nodeIntegerBound1305 : ∀ pen last, terminalScore 1305 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1305).parity (tailData 1305 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1305 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1852
  · exact terminalBound1853
  · exact terminalBound1844
  · exact terminalBound1845
theorem nodeIntegerBound1306 : ∀ pen last, terminalScore 1306 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1306).parity (tailData 1306 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1306 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1848
  · exact terminalBound1849
  · exact terminalBound1844
  · exact terminalBound1845
theorem nodeIntegerBound1307 : ∀ pen last, terminalScore 1307 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1307).parity (tailData 1307 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1307 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1828
  · exact terminalBound1829
  · exact terminalBound1872
  · exact terminalBound1847
theorem nodeIntegerBound1308 : ∀ pen last, terminalScore 1308 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1308).parity (tailData 1308 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1308 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1873
  · exact terminalBound1853
  · exact terminalBound1874
  · exact terminalBound1845
theorem nodeIntegerBound1309 : ∀ pen last, terminalScore 1309 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1309).parity (tailData 1309 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1309 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1828
  · exact terminalBound1829
  · exact terminalBound1875
  · exact terminalBound1876
theorem nodeIntegerBound1310 : ∀ pen last, terminalScore 1310 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1310).parity (tailData 1310 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1310 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1877
  · exact terminalBound1851
  · exact terminalBound1295
  · exact terminalBound1269
theorem nodeIntegerBound1311 : ∀ pen last, terminalScore 1311 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1311).parity (tailData 1311 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1311 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1878
  · exact terminalBound1855
  · exact terminalBound1874
  · exact terminalBound1845
theorem nodeIntegerBound1312 : ∀ pen last, terminalScore 1312 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1312).parity (tailData 1312 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1312 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1293
  · exact terminalBound1275
  · exact terminalBound1288
  · exact terminalBound1259
theorem nodeIntegerBound1313 : ∀ pen last, terminalScore 1313 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1313).parity (tailData 1313 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1313 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1879
  · exact terminalBound1880
  · exact terminalBound1881
  · exact terminalBound1869
theorem nodeIntegerBound1314 : ∀ pen last, terminalScore 1314 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1314).parity (tailData 1314 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1314 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1882
  · exact terminalBound1861
  · exact terminalBound1874
  · exact terminalBound1845
theorem nodeIntegerBound1315 : ∀ pen last, terminalScore 1315 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1315).parity (tailData 1315 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1315 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1883
  · exact terminalBound1884
  · exact terminalBound1885
  · exact terminalBound1863
theorem nodeIntegerBound1316 : ∀ pen last, terminalScore 1316 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1316).parity (tailData 1316 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1316 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1873
  · exact terminalBound1853
  · exact terminalBound1874
  · exact terminalBound1845
theorem nodeIntegerBound1317 : ∀ pen last, terminalScore 1317 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1317).parity (tailData 1317 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1317 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1836
  · exact terminalBound1837
  · exact terminalBound1886
  · exact terminalBound1865
theorem nodeIntegerBound1318 : ∀ pen last, terminalScore 1318 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1318).parity (tailData 1318 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1318 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1882
  · exact terminalBound1861
  · exact terminalBound1874
  · exact terminalBound1845
theorem nodeIntegerBound1319 : ∀ pen last, terminalScore 1319 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1319).parity (tailData 1319 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1319 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1883
  · exact terminalBound1884
  · exact terminalBound1887
  · exact terminalBound1859
theorem nodeIntegerBound1320 : ∀ pen last, terminalScore 1320 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1320).parity (tailData 1320 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1320 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1882
  · exact terminalBound1861
  · exact terminalBound1874
  · exact terminalBound1845
theorem nodeIntegerBound1321 : ∀ pen last, terminalScore 1321 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1321).parity (tailData 1321 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1321 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1878
  · exact terminalBound1855
  · exact terminalBound1882
  · exact terminalBound1861
theorem nodeIntegerBound1322 : ∀ pen last, terminalScore 1322 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1322).parity (tailData 1322 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1322 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1882
  · exact terminalBound1861
  · exact terminalBound1874
  · exact terminalBound1845
theorem nodeIntegerBound1323 : ∀ pen last, terminalScore 1323 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1323).parity (tailData 1323 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1323 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1888
  · exact terminalBound1849
  · exact terminalBound1874
  · exact terminalBound1845
theorem nodeIntegerBound1324 : ∀ pen last, terminalScore 1324 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1324).parity (tailData 1324 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1324 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1883
  · exact terminalBound1884
  · exact terminalBound1889
  · exact terminalBound1859
theorem nodeIntegerBound1325 : ∀ pen last, terminalScore 1325 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1325).parity (tailData 1325 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1325 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1890
  · exact terminalBound1853
  · exact terminalBound1891
  · exact terminalBound1845
theorem nodeIntegerBound1326 : ∀ pen last, terminalScore 1326 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1326).parity (tailData 1326 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1326 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1892
  · exact terminalBound1893
  · exact terminalBound1894
  · exact terminalBound1847
theorem nodeIntegerBound1327 : ∀ pen last, terminalScore 1327 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1327).parity (tailData 1327 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1327 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1895
  · exact terminalBound1841
  · exact terminalBound1896
  · exact terminalBound1279
theorem nodeIntegerBound1328 : ∀ pen last, terminalScore 1328 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1328).parity (tailData 1328 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1328 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1897
  · exact terminalBound1861
  · exact terminalBound1891
  · exact terminalBound1845
theorem nodeIntegerBound1329 : ∀ pen last, terminalScore 1329 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1329).parity (tailData 1329 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1329 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1752
  · exact terminalBound1275
  · exact terminalBound1300
  · exact terminalBound1259
theorem nodeIntegerBound1330 : ∀ pen last, terminalScore 1330 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1330).parity (tailData 1330 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1330 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1301
  · exact terminalBound1249
  · exact terminalBound1898
  · exact terminalBound1833
theorem nodeIntegerBound1331 : ∀ pen last, terminalScore 1331 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1331).parity (tailData 1331 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1331 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1899
  · exact terminalBound1843
  · exact terminalBound1900
  · exact terminalBound1861
theorem nodeIntegerBound1332 : ∀ pen last, terminalScore 1332 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1332).parity (tailData 1332 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1332 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1901
  · exact terminalBound1843
  · exact terminalBound1891
  · exact terminalBound1845
theorem nodeIntegerBound1333 : ∀ pen last, terminalScore 1333 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1333).parity (tailData 1333 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1333 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1902
  · exact terminalBound1903
  · exact terminalBound1904
  · exact terminalBound1865
theorem nodeIntegerBound1334 : ∀ pen last, terminalScore 1334 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1334).parity (tailData 1334 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1334 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1890
  · exact terminalBound1853
  · exact terminalBound1891
  · exact terminalBound1845
theorem nodeIntegerBound1335 : ∀ pen last, terminalScore 1335 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1335).parity (tailData 1335 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1335 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1899
  · exact terminalBound1843
  · exact terminalBound1905
  · exact terminalBound1845
theorem nodeIntegerBound1336 : ∀ pen last, terminalScore 1336 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1336).parity (tailData 1336 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1336 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1752
  · exact terminalBound1275
  · exact terminalBound1300
  · exact terminalBound1259
theorem nodeIntegerBound1337 : ∀ pen last, terminalScore 1337 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1337).parity (tailData 1337 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1337 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1906
  · exact terminalBound1833
  · exact terminalBound1907
  · exact terminalBound1833
theorem nodeIntegerBound1338 : ∀ pen last, terminalScore 1338 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1338).parity (tailData 1338 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1338 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1908
  · exact terminalBound1861
  · exact terminalBound1891
  · exact terminalBound1845
theorem nodeIntegerBound1339 : ∀ pen last, terminalScore 1339 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1339).parity (tailData 1339 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1339 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1906
  · exact terminalBound1833
  · exact terminalBound1909
  · exact terminalBound1281
theorem nodeIntegerBound1340 : ∀ pen last, terminalScore 1340 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1340).parity (tailData 1340 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1340 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1752
  · exact terminalBound1275
  · exact terminalBound1300
  · exact terminalBound1259
theorem nodeIntegerBound1341 : ∀ pen last, terminalScore 1341 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1341).parity (tailData 1341 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1341 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1306
  · exact terminalBound1247
  · exact terminalBound1910
  · exact terminalBound1247
theorem nodeIntegerBound1342 : ∀ pen last, terminalScore 1342 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1342).parity (tailData 1342 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1342 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1911
  · exact terminalBound1833
  · exact terminalBound1912
  · exact terminalBound1251
theorem nodeIntegerBound1343 : ∀ pen last, terminalScore 1343 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1343).parity (tailData 1343 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1343 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1892
  · exact terminalBound1893
  · exact terminalBound1913
  · exact terminalBound1831
theorem nodeIntegerBound1344 : ∀ pen last, terminalScore 1344 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1344).parity (tailData 1344 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1344 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1907
  · exact terminalBound1833
  · exact terminalBound1912
  · exact terminalBound1251
theorem nodeIntegerBound1345 : ∀ pen last, terminalScore 1345 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1345).parity (tailData 1345 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1345 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1914
  · exact terminalBound1851
  · exact terminalBound1915
  · exact terminalBound1269
theorem nodeIntegerBound1346 : ∀ pen last, terminalScore 1346 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1346).parity (tailData 1346 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1346 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1916
  · exact terminalBound1861
  · exact terminalBound1891
  · exact terminalBound1845
theorem nodeIntegerBound1347 : ∀ pen last, terminalScore 1347 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1347).parity (tailData 1347 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1347 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1892
  · exact terminalBound1893
  · exact terminalBound1917
  · exact terminalBound1876
theorem nodeIntegerBound1348 : ∀ pen last, terminalScore 1348 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1348).parity (tailData 1348 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1348 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1918
  · exact terminalBound1851
  · exact terminalBound1915
  · exact terminalBound1269
theorem nodeIntegerBound1349 : ∀ pen last, terminalScore 1349 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1349).parity (tailData 1349 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1349 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1919
  · exact terminalBound1841
  · exact terminalBound1895
  · exact terminalBound1841
theorem nodeIntegerBound1350 : ∀ pen last, terminalScore 1350 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1350).parity (tailData 1350 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1350 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1916
  · exact terminalBound1861
  · exact terminalBound1891
  · exact terminalBound1845
theorem nodeIntegerBound1351 : ∀ pen last, terminalScore 1351 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1351).parity (tailData 1351 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1351 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1919
  · exact terminalBound1841
  · exact terminalBound1896
  · exact terminalBound1279
theorem nodeIntegerBound1352 : ∀ pen last, terminalScore 1352 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1352).parity (tailData 1352 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1352 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1309
  · exact terminalBound1275
  · exact terminalBound1300
  · exact terminalBound1259
theorem nodeIntegerBound1353 : ∀ pen last, terminalScore 1353 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1353).parity (tailData 1353 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1353 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1906
  · exact terminalBound1833
  · exact terminalBound1912
  · exact terminalBound1251
theorem nodeIntegerBound1354 : ∀ pen last, terminalScore 1354 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1354).parity (tailData 1354 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1354 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1907
  · exact terminalBound1833
  · exact terminalBound1912
  · exact terminalBound1251
theorem nodeIntegerBound1355 : ∀ pen last, terminalScore 1355 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1355).parity (tailData 1355 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1355 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1897
  · exact terminalBound1861
  · exact terminalBound1891
  · exact terminalBound1845
theorem nodeIntegerBound1356 : ∀ pen last, terminalScore 1356 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1356).parity (tailData 1356 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1356 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1305
  · exact terminalBound1275
  · exact terminalBound1752
  · exact terminalBound1275
theorem nodeIntegerBound1357 : ∀ pen last, terminalScore 1357 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1357).parity (tailData 1357 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1357 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1752
  · exact terminalBound1275
  · exact terminalBound1300
  · exact terminalBound1259
theorem nodeIntegerBound1358 : ∀ pen last, terminalScore 1358 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1358).parity (tailData 1358 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1358 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1920
  · exact terminalBound1249
  · exact terminalBound1912
  · exact terminalBound1251
theorem nodeIntegerBound1359 : ∀ pen last, terminalScore 1359 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1359).parity (tailData 1359 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1359 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1898
  · exact terminalBound1833
  · exact terminalBound1317
  · exact terminalBound1251
theorem nodeIntegerBound1360 : ∀ pen last, terminalScore 1360 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1360).parity (tailData 1360 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1360 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1906
  · exact terminalBound1833
  · exact terminalBound1912
  · exact terminalBound1251
theorem nodeIntegerBound1361 : ∀ pen last, terminalScore 1361 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1361).parity (tailData 1361 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1361 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1147
  · exact terminalBound1245
  · exact terminalBound1316
  · exact terminalBound0638
theorem nodeIntegerBound1362 : ∀ pen last, terminalScore 1362 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1362).parity (tailData 1362 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1362 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1902
  · exact terminalBound1903
  · exact terminalBound1921
  · exact terminalBound1839
theorem nodeIntegerBound1363 : ∀ pen last, terminalScore 1363 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1363).parity (tailData 1363 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1363 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1907
  · exact terminalBound1833
  · exact terminalBound1912
  · exact terminalBound1251
theorem nodeIntegerBound1364 : ∀ pen last, terminalScore 1364 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1364).parity (tailData 1364 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1364 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1902
  · exact terminalBound1903
  · exact terminalBound1922
  · exact terminalBound1839
theorem nodeIntegerBound1365 : ∀ pen last, terminalScore 1365 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1365).parity (tailData 1365 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1365 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1920
  · exact terminalBound1249
  · exact terminalBound1912
  · exact terminalBound1251
theorem nodeIntegerBound1366 : ∀ pen last, terminalScore 1366 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1366).parity (tailData 1366 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1366 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1899
  · exact terminalBound1843
  · exact terminalBound1923
  · exact terminalBound1845
theorem nodeIntegerBound1367 : ∀ pen last, terminalScore 1367 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1367).parity (tailData 1367 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1367 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1924
  · exact terminalBound1853
  · exact terminalBound1925
  · exact terminalBound1845
theorem nodeIntegerBound1368 : ∀ pen last, terminalScore 1368 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1368).parity (tailData 1368 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1368 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1752
  · exact terminalBound1275
  · exact terminalBound1300
  · exact terminalBound1259
theorem nodeIntegerBound1369 : ∀ pen last, terminalScore 1369 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1369).parity (tailData 1369 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1369 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1902
  · exact terminalBound1903
  · exact terminalBound1926
  · exact terminalBound1865
theorem nodeIntegerBound1370 : ∀ pen last, terminalScore 1370 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1370).parity (tailData 1370 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1370 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1900
  · exact terminalBound1861
  · exact terminalBound1923
  · exact terminalBound1845
theorem nodeIntegerBound1371 : ∀ pen last, terminalScore 1371 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1371).parity (tailData 1371 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1371 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1924
  · exact terminalBound1853
  · exact terminalBound1927
  · exact terminalBound1861
theorem nodeIntegerBound1372 : ∀ pen last, terminalScore 1372 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1372).parity (tailData 1372 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1372 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1890
  · exact terminalBound1853
  · exact terminalBound1891
  · exact terminalBound1845
theorem nodeIntegerBound1373 : ∀ pen last, terminalScore 1373 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1373).parity (tailData 1373 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1373 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1901
  · exact terminalBound1843
  · exact terminalBound1891
  · exact terminalBound1845
theorem nodeIntegerBound1374 : ∀ pen last, terminalScore 1374 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1374).parity (tailData 1374 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1374 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1928
  · exact terminalBound1853
  · exact terminalBound1923
  · exact terminalBound1845
theorem nodeIntegerBound1375 : ∀ pen last, terminalScore 1375 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1375).parity (tailData 1375 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1375 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1910
  · exact terminalBound1247
  · exact terminalBound1307
  · exact terminalBound1241
theorem nodeIntegerBound1376 : ∀ pen last, terminalScore 1376 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1376).parity (tailData 1376 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1376 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1892
  · exact terminalBound1893
  · exact terminalBound1929
  · exact terminalBound1835
theorem nodeIntegerBound1377 : ∀ pen last, terminalScore 1377 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1377).parity (tailData 1377 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1377 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1911
  · exact terminalBound1833
  · exact terminalBound1912
  · exact terminalBound1251
theorem nodeIntegerBound1378 : ∀ pen last, terminalScore 1378 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1378).parity (tailData 1378 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1378 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1930
  · exact terminalBound1931
  · exact terminalBound1932
  · exact terminalBound1933
theorem nodeIntegerBound1379 : ∀ pen last, terminalScore 1379 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1379).parity (tailData 1379 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1379 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1934
  · exact terminalBound1931
  · exact terminalBound1935
  · exact terminalBound1936
theorem nodeIntegerBound1380 : ∀ pen last, terminalScore 1380 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1380).parity (tailData 1380 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1380 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1937
  · exact terminalBound1337
  · exact terminalBound1338
  · exact terminalBound1339
theorem nodeIntegerBound1381 : ∀ pen last, terminalScore 1381 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1381).parity (tailData 1381 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1381 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1938
  · exact terminalBound1939
  · exact terminalBound1940
  · exact terminalBound1941
theorem nodeIntegerBound1382 : ∀ pen last, terminalScore 1382 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1382).parity (tailData 1382 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1382 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1934
  · exact terminalBound1931
  · exact terminalBound1932
  · exact terminalBound1933
theorem nodeIntegerBound1383 : ∀ pen last, terminalScore 1383 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1383).parity (tailData 1383 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1383 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1343
  · exact terminalBound1337
  · exact terminalBound1338
  · exact terminalBound1339
theorem nodeIntegerBound1384 : ∀ pen last, terminalScore 1384 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1384).parity (tailData 1384 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1384 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1906
  · exact terminalBound1833
  · exact terminalBound1775
  · exact terminalBound1942
theorem nodeIntegerBound1385 : ∀ pen last, terminalScore 1385 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1385).parity (tailData 1385 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1385 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1937
  · exact terminalBound1337
  · exact terminalBound1338
  · exact terminalBound1339
theorem nodeIntegerBound1386 : ∀ pen last, terminalScore 1386 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1386).parity (tailData 1386 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1386 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1892
  · exact terminalBound1893
  · exact terminalBound1943
  · exact terminalBound1944
theorem nodeIntegerBound1387 : ∀ pen last, terminalScore 1387 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1387).parity (tailData 1387 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1387 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1945
  · exact terminalBound1946
  · exact terminalBound1947
  · exact terminalBound1948
theorem nodeIntegerBound1388 : ∀ pen last, terminalScore 1388 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1388).parity (tailData 1388 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1388 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1892
  · exact terminalBound1893
  · exact terminalBound1949
  · exact terminalBound1950
theorem nodeIntegerBound1389 : ∀ pen last, terminalScore 1389 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1389).parity (tailData 1389 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1389 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1951
  · exact terminalBound1931
  · exact terminalBound1932
  · exact terminalBound1933
theorem nodeIntegerBound1390 : ∀ pen last, terminalScore 1390 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1390).parity (tailData 1390 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1390 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1952
  · exact terminalBound1946
  · exact terminalBound1947
  · exact terminalBound1948
theorem nodeIntegerBound1391 : ∀ pen last, terminalScore 1391 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1391).parity (tailData 1391 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1391 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1937
  · exact terminalBound1337
  · exact terminalBound1338
  · exact terminalBound1339
theorem nodeIntegerBound1392 : ∀ pen last, terminalScore 1392 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1392).parity (tailData 1392 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1392 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1934
  · exact terminalBound1931
  · exact terminalBound1951
  · exact terminalBound1931
theorem nodeIntegerBound1393 : ∀ pen last, terminalScore 1393 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1393).parity (tailData 1393 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1393 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1953
  · exact terminalBound1946
  · exact terminalBound1947
  · exact terminalBound1948
theorem nodeIntegerBound1394 : ∀ pen last, terminalScore 1394 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1394).parity (tailData 1394 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1394 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1954
  · exact terminalBound1946
  · exact terminalBound1947
  · exact terminalBound1948
theorem nodeIntegerBound1395 : ∀ pen last, terminalScore 1395 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1395).parity (tailData 1395 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1395 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1953
  · exact terminalBound1946
  · exact terminalBound1947
  · exact terminalBound1948
theorem nodeIntegerBound1396 : ∀ pen last, terminalScore 1396 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1396).parity (tailData 1396 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1396 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1955
  · exact terminalBound1939
  · exact terminalBound1940
  · exact terminalBound1941
theorem nodeIntegerBound1397 : ∀ pen last, terminalScore 1397 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1397).parity (tailData 1397 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1397 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1952
  · exact terminalBound1946
  · exact terminalBound1947
  · exact terminalBound1948
theorem nodeIntegerBound1398 : ∀ pen last, terminalScore 1398 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1398).parity (tailData 1398 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1398 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1341
  · exact terminalBound1337
  · exact terminalBound1937
  · exact terminalBound1337
theorem nodeIntegerBound1399 : ∀ pen last, terminalScore 1399 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1399).parity (tailData 1399 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1399 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1937
  · exact terminalBound1337
  · exact terminalBound1338
  · exact terminalBound1339
theorem nodeIntegerBound1400 : ∀ pen last, terminalScore 1400 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1400).parity (tailData 1400 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1400 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1919
  · exact terminalBound1841
  · exact terminalBound1896
  · exact terminalBound1279
theorem nodeIntegerBound1401 : ∀ pen last, terminalScore 1401 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1401).parity (tailData 1401 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1401 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1956
  · exact terminalBound1851
  · exact terminalBound1957
  · exact terminalBound1283
theorem nodeIntegerBound1402 : ∀ pen last, terminalScore 1402 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1402).parity (tailData 1402 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1402 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1752
  · exact terminalBound1275
  · exact terminalBound1300
  · exact terminalBound1259
theorem nodeIntegerBound1403 : ∀ pen last, terminalScore 1403 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1403).parity (tailData 1403 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1403 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1956
  · exact terminalBound1851
  · exact terminalBound1918
  · exact terminalBound1851
theorem nodeIntegerBound1404 : ∀ pen last, terminalScore 1404 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1404).parity (tailData 1404 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1404 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1958
  · exact terminalBound1861
  · exact terminalBound1891
  · exact terminalBound1845
theorem nodeIntegerBound1405 : ∀ pen last, terminalScore 1405 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1405).parity (tailData 1405 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1405 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1959
  · exact terminalBound1960
  · exact terminalBound1961
  · exact terminalBound1962
theorem nodeIntegerBound1406 : ∀ pen last, terminalScore 1406 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1406).parity (tailData 1406 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1406 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1963
  · exact terminalBound1964
  · exact terminalBound1965
  · exact terminalBound1966
theorem nodeIntegerBound1407 : ∀ pen last, terminalScore 1407 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1407).parity (tailData 1407 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1407 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1967
  · exact terminalBound1968
  · exact terminalBound1969
  · exact terminalBound1970

end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
