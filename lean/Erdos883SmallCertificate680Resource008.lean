import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_8 :
    (List.ofFn coreChunks680_8).flatten =
      (coreData680.take (coreResources680 8).q).drop 121 := by
  decide +kernel

theorem coreCheck680_8 :
    ∀ c : Fin 1, (coreChunks680_8 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 8)) = true := by
  decide +kernel
#print axioms coreFlatten680_8
#print axioms coreCheck680_8
end Erdos883Verified
