import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_139 :
    (List.ofFn coreChunks908_139).flatten =
      (coreData908.take (coreResources908 139).q).drop 256 := by
  decide +kernel

theorem coreCheck908_139 :
    ∀ c : Fin 1, (coreChunks908_139 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 139)) = true := by
  decide +kernel
#print axioms coreFlatten908_139
#print axioms coreCheck908_139
end Erdos883Verified
