import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_44 :
    (List.ofFn coreChunks749_44).flatten =
      (coreData749.take (coreResources749 44).q).drop 173 := by
  decide +kernel

theorem coreCheck749_44 :
    ∀ c : Fin 1, (coreChunks749_44 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 44)) = true := by
  decide +kernel
#print axioms coreFlatten749_44
#print axioms coreCheck749_44
end Erdos883Verified
