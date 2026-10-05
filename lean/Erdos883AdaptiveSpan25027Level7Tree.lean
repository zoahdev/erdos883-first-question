import Erdos883AdaptiveSpan25027Level7TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength25027_7 : adaptiveNumericSpans25027_7.length = 450 := by decide +kernel
theorem adaptiveSpanEvenCache25027_7 : adaptiveSpanEven25027_7.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain25027_7 : adaptiveSpanEven25027_7.domainCheck 12514 = true := by decide +kernel
theorem adaptiveSpanEvenEntries25027_7 : adaptiveSpanEven25027_7.spans = coreEvenSpans 12514 0 adaptiveNumericSpans25027_7 := by
  decide +kernel
theorem adaptiveSpanWholeCache25027_7 : adaptiveSpanWhole25027_7.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain25027_7 : adaptiveSpanWhole25027_7.domainCheck 12514 = true := by decide +kernel
theorem adaptiveSpanWholeEntries25027_7 : adaptiveSpanWhole25027_7.spans = coreWholeSpans 0 adaptiveNumericSpans25027_7 := by
  decide +kernel
end Erdos883Verified
