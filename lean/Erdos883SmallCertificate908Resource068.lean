import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_68 :
    (List.ofFn coreChunks908_68).flatten =
      (coreData908.take (coreResources908 68).q).drop 129 := by
  decide +kernel

theorem coreCheck908_68 :
    ∀ c : Fin 1, (coreChunks908_68 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 68)) = true := by
  decide +kernel
#print axioms coreFlatten908_68
#print axioms coreCheck908_68
end Erdos883Verified
