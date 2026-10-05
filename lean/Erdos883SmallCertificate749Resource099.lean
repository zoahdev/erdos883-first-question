import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_99 :
    (List.ofFn coreChunks749_99).flatten =
      (coreData749.take (coreResources749 99).q).drop 172 := by
  decide +kernel

theorem coreCheck749_99 :
    ∀ c : Fin 1, (coreChunks749_99 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 99)) = true := by
  decide +kernel
#print axioms coreFlatten749_99
#print axioms coreCheck749_99
end Erdos883Verified
