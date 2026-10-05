import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_55 :
    (List.ofFn coreChunks680_55).flatten =
      (coreData680.take (coreResources680 55).q).drop 111 := by
  decide +kernel

theorem coreCheck680_55 :
    ∀ c : Fin 1, (coreChunks680_55 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 55)) = true := by
  decide +kernel
#print axioms coreFlatten680_55
#print axioms coreCheck680_55
end Erdos883Verified
