import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_38 :
    (List.ofFn coreChunks908_38).flatten =
      (coreData908.take (coreResources908 38).q).drop 190 := by
  decide +kernel

theorem coreCheck908_38 :
    ∀ c : Fin 1, (coreChunks908_38 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 38)) = true := by
  decide +kernel
#print axioms coreFlatten908_38
#print axioms coreCheck908_38
end Erdos883Verified
