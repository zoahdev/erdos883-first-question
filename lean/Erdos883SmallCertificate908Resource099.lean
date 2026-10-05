import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_99 :
    (List.ofFn coreChunks908_99).flatten =
      (coreData908.take (coreResources908 99).q).drop 172 := by
  decide +kernel

theorem coreCheck908_99 :
    ∀ c : Fin 1, (coreChunks908_99 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 99)) = true := by
  decide +kernel
#print axioms coreFlatten908_99
#print axioms coreCheck908_99
end Erdos883Verified
