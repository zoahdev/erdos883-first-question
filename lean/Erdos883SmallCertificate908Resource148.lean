import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_148 :
    (List.ofFn coreChunks908_148).flatten =
      (coreData908.take (coreResources908 148).q).drop 285 := by
  decide +kernel

theorem coreCheck908_148 :
    ∀ c : Fin 1, (coreChunks908_148 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 148)) = true := by
  decide +kernel
#print axioms coreFlatten908_148
#print axioms coreCheck908_148
end Erdos883Verified
