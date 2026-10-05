import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_151 :
    (List.ofFn coreChunks908_151).flatten =
      (coreData908.take (coreResources908 151).q).drop 298 := by
  decide +kernel

theorem coreCheck908_151 :
    ∀ c : Fin 1, (coreChunks908_151 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 151)) = true := by
  decide +kernel
#print axioms coreFlatten908_151
#print axioms coreCheck908_151
end Erdos883Verified
