import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_91 :
    (List.ofFn coreChunks908_91).flatten =
      (coreData908.take (coreResources908 91).q).drop 160 := by
  decide +kernel

theorem coreCheck908_91 :
    ∀ c : Fin 1, (coreChunks908_91 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 91)) = true := by
  decide +kernel
#print axioms coreFlatten908_91
#print axioms coreCheck908_91
end Erdos883Verified
