import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_144 :
    (List.ofFn coreChunks749_144).flatten =
      (coreData749.take (coreResources749 144).q).drop 242 := by
  decide +kernel

theorem coreCheck749_144 :
    ∀ c : Fin 1, (coreChunks749_144 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 144)) = true := by
  decide +kernel
#print axioms coreFlatten749_144
#print axioms coreCheck749_144
end Erdos883Verified
