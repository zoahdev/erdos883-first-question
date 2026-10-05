import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_45 :
    (List.ofFn coreChunks908_45).flatten =
      (coreData908.take (coreResources908 45).q).drop 198 := by
  decide +kernel

theorem coreCheck908_45 :
    ∀ c : Fin 1, (coreChunks908_45 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 45)) = true := by
  decide +kernel
#print axioms coreFlatten908_45
#print axioms coreCheck908_45
end Erdos883Verified
