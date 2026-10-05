import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_138 :
    (List.ofFn coreChunks908_138).flatten =
      (coreData908.take (coreResources908 138).q).drop 250 := by
  decide +kernel

theorem coreCheck908_138 :
    ∀ c : Fin 1, (coreChunks908_138 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 138)) = true := by
  decide +kernel
#print axioms coreFlatten908_138
#print axioms coreCheck908_138
end Erdos883Verified
