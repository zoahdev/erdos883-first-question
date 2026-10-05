import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_104 :
    (List.ofFn coreChunks680_104).flatten =
      (coreData680.take (coreResources680 104).q).drop 204 := by
  decide +kernel

theorem coreCheck680_104 :
    ∀ c : Fin 1, (coreChunks680_104 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 104)) = true := by
  decide +kernel
#print axioms coreFlatten680_104
#print axioms coreCheck680_104
end Erdos883Verified
