import Erdos883AdaptiveSpan104564Level6TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength104564_6 : adaptiveNumericSpans104564_6.length = 642 := by decide +kernel
theorem adaptiveSpanEvenCache104564_6 : adaptiveSpanEven104564_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain104564_6 : adaptiveSpanEven104564_6.domainCheck 52282 = true := by decide +kernel
theorem adaptiveSpanEvenEntries104564_6 : adaptiveSpanEven104564_6.spans = coreEvenSpans 52282 0 adaptiveNumericSpans104564_6 := by
  decide +kernel
theorem adaptiveSpanWholeCache104564_6 : adaptiveSpanWhole104564_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain104564_6 : adaptiveSpanWhole104564_6.domainCheck 52282 = true := by decide +kernel
theorem adaptiveSpanWholeEntries104564_6 : adaptiveSpanWhole104564_6.spans = coreWholeSpans 0 adaptiveNumericSpans104564_6 := by
  decide +kernel
end Erdos883Verified
