import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_110 :
    (List.ofFn coreChunks908_110).flatten =
      (coreData908.take (coreResources908 110).q).drop 191 := by
  decide +kernel

theorem coreCheck908_110 :
    ∀ c : Fin 1, (coreChunks908_110 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 110)) = true := by
  decide +kernel
#print axioms coreFlatten908_110
#print axioms coreCheck908_110
end Erdos883Verified
