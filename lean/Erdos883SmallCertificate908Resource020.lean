import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_20 :
    (List.ofFn coreChunks908_20).flatten =
      (coreData908.take (coreResources908 20).q).drop 167 := by
  decide +kernel

theorem coreCheck908_20 :
    ∀ c : Fin 1, (coreChunks908_20 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 20)) = true := by
  decide +kernel
#print axioms coreFlatten908_20
#print axioms coreCheck908_20
end Erdos883Verified
