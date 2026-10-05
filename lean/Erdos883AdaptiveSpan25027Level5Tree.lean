import Erdos883AdaptiveSpan25027Level5TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength25027_5 : adaptiveNumericSpans25027_5.length = 450 := by decide +kernel
theorem adaptiveSpanEvenCache25027_5 : adaptiveSpanEven25027_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain25027_5 : adaptiveSpanEven25027_5.domainCheck 12514 = true := by decide +kernel
theorem adaptiveSpanEvenEntries25027_5 : adaptiveSpanEven25027_5.spans = coreEvenSpans 12514 0 adaptiveNumericSpans25027_5 := by
  decide +kernel
theorem adaptiveSpanWholeCache25027_5 : adaptiveSpanWhole25027_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain25027_5 : adaptiveSpanWhole25027_5.domainCheck 12514 = true := by decide +kernel
theorem adaptiveSpanWholeEntries25027_5 : adaptiveSpanWhole25027_5.spans = coreWholeSpans 0 adaptiveNumericSpans25027_5 := by
  decide +kernel
end Erdos883Verified
