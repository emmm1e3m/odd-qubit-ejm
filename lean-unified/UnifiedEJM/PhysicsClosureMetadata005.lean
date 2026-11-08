import UnifiedEJM.PhysicsClosureMetadataDefinition
import UnifiedEJM.PhysicsClosureAggregation

open OddEJM
open scoped BigOperators
namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
open UnifiedEJM.PathCutScore
open UnifiedEJM.ClosureAggregation
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem nodeMetadataSlice020 : FinSlice NodeMetadata 1280 64 := by
  intro i hi
  fin_cases i
  · exact (show NodeMetadata (1280 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1281 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1282 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1283 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1284 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1285 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1286 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1287 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1288 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1289 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1290 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1291 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1292 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1293 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1294 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1295 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1296 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1297 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1298 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1299 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1300 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1301 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1302 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1303 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1304 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1305 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1306 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1307 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1308 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1309 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1310 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1311 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1312 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1313 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1314 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1315 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1316 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1317 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1318 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1319 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1320 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1321 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1322 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1323 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1324 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1325 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1326 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1327 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1328 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1329 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1330 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1331 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1332 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1333 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1334 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1335 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1336 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1337 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1338 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1339 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1340 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1341 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1342 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1343 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)

theorem nodeMetadataSlice021 : FinSlice NodeMetadata 1344 64 := by
  intro i hi
  fin_cases i
  · exact (show NodeMetadata (1344 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1345 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1346 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1347 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1348 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1349 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1350 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1351 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1352 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1353 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1354 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1355 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1356 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1357 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1358 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1359 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1360 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1361 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1362 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1363 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1364 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1365 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1366 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1367 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1368 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1369 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1370 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1371 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1372 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1373 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1374 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1375 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1376 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1377 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1378 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1379 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1380 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1381 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1382 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1383 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1384 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1385 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1386 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1387 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1388 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1389 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1390 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1391 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1392 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1393 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1394 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1395 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1396 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1397 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1398 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1399 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1400 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1401 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1402 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1403 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1404 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1405 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1406 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1407 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)

theorem nodeMetadataSlice022 : FinSlice NodeMetadata 1408 64 := by
  intro i hi
  fin_cases i
  · exact (show NodeMetadata (1408 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1409 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1410 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1411 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1412 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1413 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1414 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1415 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1416 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1417 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1418 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1419 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1420 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1421 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1422 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1423 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1424 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1425 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1426 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1427 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1428 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1429 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1430 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1431 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1432 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1433 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1434 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1435 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1436 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1437 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1438 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1439 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1440 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1441 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1442 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1443 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1444 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1445 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1446 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1447 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1448 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1449 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1450 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1451 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1452 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1453 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1454 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1455 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1456 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1457 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1458 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1459 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1460 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1461 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1462 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1463 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1464 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1465 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1466 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1467 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1468 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1469 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1470 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1471 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)

theorem nodeMetadataSlice023 : FinSlice NodeMetadata 1472 64 := by
  intro i hi
  fin_cases i
  · exact (show NodeMetadata (1472 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1473 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1474 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1475 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1476 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1477 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1478 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1479 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1480 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1481 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1482 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1483 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1484 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1485 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1486 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1487 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1488 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1489 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1490 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1491 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1492 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1493 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1494 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1495 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1496 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1497 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1498 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1499 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1500 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1501 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1502 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1503 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1504 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1505 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1506 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1507 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1508 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1509 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1510 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1511 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1512 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1513 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1514 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1515 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1516 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1517 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1518 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1519 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1520 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1521 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1522 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1523 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1524 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1525 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1526 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1527 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1528 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1529 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1530 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1531 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1532 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1533 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1534 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1535 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
