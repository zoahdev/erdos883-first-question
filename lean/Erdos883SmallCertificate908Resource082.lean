import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_82 :
    (List.ofFn coreChunks908_82).flatten =
      (coreData908.take (coreResources908 82).q).drop 148 := by
  decide +kernel

theorem coreCheck908_82 :
    ∀ c : Fin 1, (coreChunks908_82 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 82)) = true := by
  decide +kernel
#print axioms coreFlatten908_82
#print axioms coreCheck908_82
end Erdos883Verified
