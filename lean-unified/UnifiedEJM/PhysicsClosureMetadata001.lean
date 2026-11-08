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

theorem nodeMetadataSlice004 : FinSlice NodeMetadata 256 64 := by
  intro i hi
  fin_cases i
  · exact (show NodeMetadata (256 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (257 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (258 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (259 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (260 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (261 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (262 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (263 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (264 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (265 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (266 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (267 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (268 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (269 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (270 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (271 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (272 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (273 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (274 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (275 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (276 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (277 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (278 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (279 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (280 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (281 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (282 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (283 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (284 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (285 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (286 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (287 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (288 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (289 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (290 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (291 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (292 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (293 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (294 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (295 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (296 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (297 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (298 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (299 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (300 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (301 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (302 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (303 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (304 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (305 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (306 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (307 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (308 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (309 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (310 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (311 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (312 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (313 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (314 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (315 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (316 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (317 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (318 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (319 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)

theorem nodeMetadataSlice005 : FinSlice NodeMetadata 320 64 := by
  intro i hi
  fin_cases i
  · exact (show NodeMetadata (320 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (321 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (322 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (323 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (324 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (325 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (326 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (327 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (328 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (329 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (330 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (331 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (332 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (333 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (334 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (335 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (336 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (337 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (338 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (339 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (340 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (341 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (342 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (343 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (344 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (345 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (346 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (347 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (348 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (349 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (350 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (351 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (352 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (353 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (354 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (355 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (356 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (357 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (358 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (359 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (360 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (361 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (362 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (363 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (364 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (365 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (366 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (367 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (368 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (369 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (370 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (371 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (372 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (373 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (374 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (375 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (376 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (377 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (378 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (379 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (380 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (381 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (382 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (383 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)

theorem nodeMetadataSlice006 : FinSlice NodeMetadata 384 64 := by
  intro i hi
  fin_cases i
  · exact (show NodeMetadata (384 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (385 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (386 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (387 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (388 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (389 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (390 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (391 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (392 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (393 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (394 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (395 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (396 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (397 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (398 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (399 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (400 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (401 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (402 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (403 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (404 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (405 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (406 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (407 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (408 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (409 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (410 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (411 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (412 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (413 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (414 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (415 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (416 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (417 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (418 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (419 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (420 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (421 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (422 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (423 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (424 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (425 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (426 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (427 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (428 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (429 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (430 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (431 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (432 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (433 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (434 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (435 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (436 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (437 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (438 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (439 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (440 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (441 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (442 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (443 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (444 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (445 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (446 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (447 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)

theorem nodeMetadataSlice007 : FinSlice NodeMetadata 448 64 := by
  intro i hi
  fin_cases i
  · exact (show NodeMetadata (448 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (449 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (450 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (451 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (452 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (453 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (454 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (455 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (456 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (457 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (458 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (459 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (460 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (461 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (462 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (463 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (464 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (465 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (466 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (467 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (468 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (469 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (470 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (471 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (472 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (473 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (474 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (475 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (476 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (477 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (478 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (479 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (480 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (481 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (482 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (483 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (484 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (485 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (486 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (487 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (488 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (489 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (490 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (491 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (492 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (493 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (494 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (495 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (496 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (497 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (498 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (499 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (500 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (501 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (502 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (503 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (504 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (505 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (506 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (507 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (508 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (509 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (510 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (511 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
