import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_149 :
    (List.ofFn coreChunks908_149).flatten =
      (coreData908.take (coreResources908 149).q).drop 287 := by
  decide +kernel

theorem coreCheck908_149 :
    ∀ c : Fin 1, (coreChunks908_149 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 149)) = true := by
  decide +kernel
#print axioms coreFlatten908_149
#print axioms coreCheck908_149
end Erdos883Verified
