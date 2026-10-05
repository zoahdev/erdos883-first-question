import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_78 :
    (List.ofFn coreChunks908_78).flatten =
      (coreData908.take (coreResources908 78).q).drop 143 := by
  decide +kernel

theorem coreCheck908_78 :
    ∀ c : Fin 1, (coreChunks908_78 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 78)) = true := by
  decide +kernel
#print axioms coreFlatten908_78
#print axioms coreCheck908_78
end Erdos883Verified
