import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_137 :
    (List.ofFn coreChunks908_137).flatten =
      (coreData908.take (coreResources908 137).q).drop 241 := by
  decide +kernel

theorem coreCheck908_137 :
    ∀ c : Fin 1, (coreChunks908_137 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 137)) = true := by
  decide +kernel
#print axioms coreFlatten908_137
#print axioms coreCheck908_137
end Erdos883Verified
