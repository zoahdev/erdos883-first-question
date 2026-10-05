import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_46 :
    (List.ofFn coreChunks618_46).flatten =
      (coreData618.take (coreResources618 46).q).drop 100 := by
  decide +kernel

theorem coreCheck618_46 :
    ∀ c : Fin 1, (coreChunks618_46 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 46)) = true := by
  decide +kernel
#print axioms coreFlatten618_46
#print axioms coreCheck618_46
end Erdos883Verified
