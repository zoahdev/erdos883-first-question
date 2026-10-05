import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_135 :
    (List.ofFn coreChunks908_135).flatten =
      (coreData908.take (coreResources908 135).q).drop 235 := by
  decide +kernel

theorem coreCheck908_135 :
    ∀ c : Fin 1, (coreChunks908_135 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 135)) = true := by
  decide +kernel
#print axioms coreFlatten908_135
#print axioms coreCheck908_135
end Erdos883Verified
