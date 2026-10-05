import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_105 :
    (List.ofFn coreChunks680_105).flatten =
      (coreData680.take (coreResources680 105).q).drop 206 := by
  decide +kernel

theorem coreCheck680_105 :
    ∀ c : Fin 1, (coreChunks680_105 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 105)) = true := by
  decide +kernel
#print axioms coreFlatten680_105
#print axioms coreCheck680_105
end Erdos883Verified
